-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_theorem_4_1
-- name    : CNFLearning873.Valiant.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:11:40.126911+00:00
-- url     : https://prove2.me/theorems/1448bbe5-06eb-4034-9ac1-387d1dffcd3d
-- title:
--   Theorem 4.1 — Valiant’s full sample and time bounds
-- statement:
--   Fix integers $k\ge100,d\ge1$ and any real $t\ge1$ satisfying condition (2). There are positive constants $C_{\rm sample},C_{\rm time}$ and an integer $n_0\ge k$, depending only on $k,d,t$. For every $n$, every $0<\varepsilon,\delta<1$, and every $n$-variable $(k,d)$-CNF $F$, Valiant's actual enumeration/filter algorithm learns $F$ with
--
--   $$\Pr_{(X_i)\sim\mu_F^{\otimes N}}\{d_{\rm TV}(\mu_F,\mu_{\widehat F})\le\varepsilon\}\ge1-\delta.$$
--
--   The success event includes nonemptiness of the output's solution set. For $n\ge k$, use the deterministic sample choice
--
--   $$N_{\rm chosen}=\max\{1,\lceil\tau^{-1}(k\ln(2n)+\ln(1/\delta))\rceil\},$$
--
--   with exactly Equation (4)'s computed $M,\lambda,\tau$. Correctness holds for every $N\ge N_{\rm chosen}$ and also for every positive integer above the displayed real threshold. For $n<k$, including $n=0$, the candidate and target families are empty; zero samples suffice. For $n\ge n_0$,
--
--   $$N_{\rm chosen}\le C_{\rm sample}\frac{n^{\lceil t\rceil}}{\varepsilon}(\ln(n/\varepsilon))^{k+1}\ln(n/\delta),$$
--   $$\operatorname{time}(n,k,(X_i)_{i=1}^N)\le C_{\rm time}n^kN\qquad(N\ge1).$$
--
--   The execution enumerates each of the $2^k\binom nk$ candidates exactly once and emits precisely the semantic survivor set. Its recursively accumulated primitive-operation count charges enumeration, sample-coordinate tests, loop steps and output construction. Only $n,k$ and samples are algorithm inputs. Constants are fixed before $n,\varepsilon,\delta,F$ and the observed sequence; neither sample count nor runtime is assumed.
--
--   Differences from the source:
--   - encoding: finite Boolean variables and forbidden assignments → Fin n and published literal-sign clauses; reason: bijective relabeling and negation of literal signs preserve every clause and assignment
--   - encoding: uniform solution distribution → an existential proof of nonempty solutions followed by the published finite uniform law; reason: satisfiability is concluded and a probability law is never placed on an empty set
--   - encoding: N = O_{k,d,t} of the printed sample scale and the sufficient real threshold in its proof → positive constants and n₀ before n, ε, δ, F with the ceiling threshold and explicit bound; reason: precise uniform asymptotic quantifiers with the finite-n correctness statement retained
--   - encoding: Valiant enumeration/filter algorithm and ordinary combinatorial running time → literal-list implementation, semantic output equality, exact enumeration, and an accumulated unit-cost operation count; reason: charges the stated loops and output with constant-time coordinate access; no bit complexity or target oracle is introduced
--   - encoding: no width-k clauses when n < k → zero chosen samples and the True output in this branch; reason: empty candidate family has exactly the target uniform law and no logarithm of n is evaluated
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, Theorem 4.1, printed p.12 = 1-based PDF p.12; proof and Equation (4), pp.13–14

import Definitions.Def_CNFLearning873_Valiant_Execution

namespace CNFLearning873.Valiant

/-- Theorem 4.1, p.12 = PDF p.12, with the explicit sufficient sample threshold
from p.14 and all of the printed sample and unit-cost time conclusions. Constants
and n₀ depend only on k,d,t, before n, error/confidence, formula and sample inputs.
The n<k branch, including n=0, requests zero samples and returns True. -/
theorem theorem_4_1 (k d : ℕ) (t : ℝ) (hk : 100 ≤ k) (hd : 1 ≤ d)
    (ht : 1 ≤ t) (hLLL : LLLCondition k d t) :
    ∃ Csample Ctime : ℝ, 0 < Csample ∧ 0 < Ctime ∧
      ∃ n₀ : ℕ, k ≤ n₀ ∧
        (∀ n : ℕ, (enumerate (List.finRange n) k).1.length = 2 ^ k * n.choose k ∧
          ((enumerate (List.finRange n) k).1.map decodeClause).Nodup ∧
          ((enumerate (List.finRange n) k).1.map decodeClause).toFinset = candidates n k) ∧
        (∀ (n N : ℕ) (xs : Fin N → Assignment n), decodedOutput k xs = output k xs) ∧
        (∀ (n N : ℕ) (xs : Fin N → Assignment n), n₀ ≤ n → 1 ≤ N →
          ((run k xs).2 : ℝ) ≤ Ctime * (n : ℝ) ^ k * (N : ℝ)) ∧
        ∀ (n : ℕ) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          (n < k → chosenSamples n k d t ε δ = 0) ∧
          (k ≤ n → 0 < parameterM n k d t ε ∧
            0 < parameterLambda n k d t ε ∧ 0 < parameterTau n k d t ε ∧
            1 ≤ chosenSamples n k d t ε δ ∧
            sampleThreshold n k d t ε δ ≤ (chosenSamples n k d t ε δ : ℝ)) ∧
          (n₀ ≤ n → (chosenSamples n k d t ε δ : ℝ) ≤
            Csample * sampleScale n k t ε δ) ∧
          ∀ F : CNF n, KD F k d →
            ∃ h : (solutions F).Nonempty,
              (∀ N : ℕ, chosenSamples n k d t ε δ ≤ N →
                1 - δ ≤ eventProb (sampleLaw F h N) (Success F h k ε)) ∧
              (∀ N : ℕ, (n < k ∨ (1 ≤ N ∧ sampleThreshold n k d t ε δ ≤ (N : ℝ))) →
                1 - δ ≤ eventProb (sampleLaw F h N) (Success F h k ε)) := by sorry

end CNFLearning873.Valiant
