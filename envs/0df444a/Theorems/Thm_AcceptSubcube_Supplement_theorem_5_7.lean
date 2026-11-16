-- Prove2me | Theorems.Thm_AcceptSubcube_Supplement_theorem_5_7
-- name    : AcceptSubcube.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:53:01.476218+00:00
-- url     : https://prove2.me/theorems/315bb364-6664-42a9-8f54-067c1d18be6e
-- title:
--   Theorem 5.7 — complete signed NAE: $O(1)$, $O(\sqrt{\log(2+\mathrm{OPT}/n)})$, $O_k((n/\log(n+2))^{k-4})$ and matching hardness
-- statement:
--   Let $\mathcal{CI}_k$ be the class of complete $k$-CSPs whose predicates are all nontrivial and invariant under complementing all inputs; it contains every complete signed $\mathrm{NAE}_k$ instance. The upper bounds hold with probability at least $1-(n+2)^{-10}$.
--
--   1. **(i)** There are $A>0$ and a randomized polynomial-time algorithm that outputs, on every instance of $\mathcal{CI}_3$, an assignment $Y$ with $C_{\mathcal I}(Y)\le A\,\mathrm{OPT}$, and whose output is optimal for every coin string when $\mathrm{OPT}\le n$.
--   2. **(ii), upper bound.** There are $A>0$ and a randomized polynomial-time algorithm with $C_{\mathcal I}(Y)\le A\sqrt{\log(2+\mathrm{OPT}/n)}\;\mathrm{OPT}$ on $\mathcal{CI}_4$.
--   3. **(iii), upper bound.** For every $k\ge5$ there are $A_k>0$ and a randomized polynomial-time algorithm with $C_{\mathcal I}(Y)\le A_k\big(n/\log(n+2)\big)^{k-4}\mathrm{OPT}$ on $\mathcal{CI}_k$.
--   4. **(ii), lower bound.** Under the UGC: if a randomized polynomial-time algorithm achieves a constant factor $\rho$ on the complete signed $\mathrm{NAE}_4$ instances with $\mathrm{OPT}\ge1$, with some fixed probability $p_0>0$ or in expectation, then $\mathsf{NP}\subseteq\mathsf{BPP}$.
--   5. **(iii), lower bound.** For $k\ge5$, $\varepsilon>0$ and $c>0$: if a randomized polynomial-time algorithm achieves the ratio $c\,n^{k-4-\varepsilon}$ on the complete signed $\mathrm{NAE}_k$ instances with $\mathrm{OPT}\ge1$, with some fixed probability $p_0>0$ or in expectation, then $\mathsf{NP}=\mathsf{RP}$.
--
--   Signed $\mathrm{NAE}_k$ has accepting-subcube dimension $k-2$, and its transitions occur one arity later than for arbitrary predicates; complement symmetry allows one variable to be pinned safely.
--
--   **Formalization Note** Machine model, coin strings, classes and UGC as in Theorems 1.1 and 1.2. Natural logarithms; $\mathrm{OPT}/n$ is real division.
--
--   Differences from the source:
--   - reading: a randomized (resp. deterministic) polynomial-time algorithm → a TM2 polynomial-time machine (Turing.TM2ComputableInPolyTime) on (instance, coin string) with coin strings of length p(|enc I|) for a polynomial p fixed before the instance, probabilities and expectations taken over the exact uniform distribution on those coin strings (resp. a TM2 polynomial-time machine on the instance alone); reason: the paper names no machine model; fair coins are its model (p.28); this is the convention of the published theorem_1_1
--   - encoding: NP, RP, BPP, P and the UGC → the classes of the published CookPvsNP model over every finite alphabet (RP and BPP as polynomial-time checking relations on (input, coin string) with coin strings of length |w|^k + k), and the published OptInapprox.MaxCut.UGC; reason: one machine model for every class in a statement, the model of the published UGC; these are the standard classes
--   - reading: a randomized polynomial-time algorithm with approximation ratio … (success probability not stated) → probability at least 1 − (n+2)^{−10}; reason: the convention of Theorem 1.1; the upper bounds are Theorem 5.1 at t = 1 (p.29), which holds with any ζ, here ζ = (n+2)^{−10}
--   - reading: exact when OPT ≤ n → the output is optimal for every coin string of the given length; reason: an exact algorithm never errs; the exact branch is the deterministic enumeration of Theorem 5.1(a)
--   - reading: The upper bounds also hold for every nontrivial predicate invariant under complementing all inputs → the upper bounds are stated on complete instances whose predicates are all nontrivial and complement-invariant (possibly different on different scopes); reason: this class contains complete signed NAE_k, so the stated bounds imply the source's; the proof (p.29) uses only property P₁, which every such predicate has (Proposition 2.3)
--   - reading: no randomized polynomial-time constant-factor approximation; no such algorithm has ratio O(n^{k−4−ε}) → no algorithm succeeding with any fixed probability p₀ > 0, or in expectation; reason: the weakest success notions the proofs cover (Lemma 7.2, §8.4), giving the strongest statement
--   - generalization: the lower bounds concern algorithms on all complete signed NAE_k instances → the algorithm is assumed only on complete signed NAE_k instances with OPT ≥ 1; reason: a weaker hypothesis gives a stronger theorem that specializes to the source (an algorithm on all instances works on these); the reductions produce instances with OPT ≥ 1 (Lemma 7.7(iii), Lemma 8.3)
--   - encoding: O(1), O(√log(2 + OPT/n)), O_k(…), O(n^{k−4−ε}) → explicit constants A, A_k > 0 on every instance; c·n^{k−4−ε} on every instance for every c > 0; reason: finitely many instances per n, so thresholds are absorbed into the constants
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 5.7, p.28 (upper bounds: p.29; lower bounds: §7.4, pp.38–40 and §8, pp.43–46)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_encInst
import Definitions.Def_AcceptSubcube_coinFrac
import Definitions.Def_AcceptSubcube_Supplement_RP
import Definitions.Def_AcceptSubcube_Supplement_CompleteSigned
import Definitions.Def_AcceptSubcube_Supplement_RandApproxOn

namespace AcceptSubcube.Supplement

open AcceptSubcube

/-- **Theorem 5.7 (Complete signed NAE).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 5.7, p.28: "(i) Complete signed NAE3
has a randomized polynomial-time constant-factor approximation, exact when OPT ≤ n. (ii) Complete
signed NAE4 has a randomized polynomial-time algorithm with approximation ratio
O(√log(2 + OPT/n)). Under the UGC and NP ⊄ BPP, it has no randomized polynomial-time
constant-factor approximation. (iii) For every fixed k ≥ 5, complete signed NAEk admits a randomized
polynomial-time algorithm with ratio O_k((n/log(n + 2))^{k−4}). Unless NP = RP, no such algorithm
has ratio O(n^{k−4−ε}) for a fixed ε > 0. The upper bounds also hold for every nontrivial predicate
invariant under complementing all inputs."

Upper bounds, on complete `k`-CSPs whose predicates are all nontrivial and complement-invariant
(`CompleteComplInv k`, which contains complete signed `NAE_k`), with probability at least
`1 − (n+2)^{−10}`:
1. `k = 3`: `C_I(Y) ≤ A·OPT`, and the output is optimal for every coin string when `OPT ≤ n`;
2. `k = 4`: `C_I(Y) ≤ A √log(2 + OPT/n) · OPT`;
3. `k ≥ 5`: `C_I(Y) ≤ A_k (n/log(n + 2))^{k−4} · OPT`.

Lower bounds, for complete signed `NAE_k` instances with `OPT ≥ 1`:
4. under the UGC, a randomized polynomial-time constant-factor approximation for `k = 4`
   (probability `≥ p₀ > 0` or in expectation) gives `NP ⊆ BPP`;
5. for `k ≥ 5`, `ε > 0`, `c > 0`, a randomized polynomial-time `c·n^{k−4−ε}`-approximation
   (probability `≥ p₀ > 0` or in expectation) gives `NP = RP`.

**Formalization Note.** Machine model, coin strings and classes as in the published `theorem_1_1`
and `theorem_1_2` of this mission. "Randomized … approximation ratio" in the upper bounds is read as
Theorem 1.1's guarantee (probability `1 − (n+2)^{−10}`); "exact" as optimal output for every coin
string. In the lower bounds the algorithm is assumed only on instances with positive optimum and
may succeed with any fixed positive probability or in expectation (the weakest hypotheses, so the
strongest statements). Natural logarithms; `OPT/n` is real division (`n ≥ 4` whenever a constraint
exists). -/
theorem theorem_5_7 :
    (∃ A : ℝ, 0 < A ∧ ∃ (p : Polynomial ℕ) (alg : GInst × List Bool → List Bool),
      Nonempty (Turing.TM2ComputableInPolyTime encInstCoins encAssign alg) ∧
      ∀ I : GInst, CompleteComplInv 3 I →
        1 - ((I.n : ℝ) + 2) ^ (-10 : ℤ) ≤
          coinProb I p (fun w => (cost I (asg I (alg (I, w))) : ℝ) ≤ A * (OPT I : ℝ)) ∧
        (OPT I ≤ I.n → ∀ w : List Bool, w.length = p.eval (encInst I).length →
          cost I (asg I (alg (I, w))) = OPT I)) ∧
    (∃ A : ℝ, 0 < A ∧ ∃ (p : Polynomial ℕ) (alg : GInst × List Bool → List Bool),
      Nonempty (Turing.TM2ComputableInPolyTime encInstCoins encAssign alg) ∧
      ∀ I : GInst, CompleteComplInv 4 I →
        1 - ((I.n : ℝ) + 2) ^ (-10 : ℤ) ≤
          coinProb I p (fun w => (cost I (asg I (alg (I, w))) : ℝ) ≤
            A * Real.sqrt (Real.log (2 + (OPT I : ℝ) / (I.n : ℝ))) * (OPT I : ℝ))) ∧
    (∀ k : ℕ, 5 ≤ k → ∃ A : ℝ, 0 < A ∧ ∃ (p : Polynomial ℕ) (alg : GInst × List Bool → List Bool),
      Nonempty (Turing.TM2ComputableInPolyTime encInstCoins encAssign alg) ∧
      ∀ I : GInst, CompleteComplInv k I →
        1 - ((I.n : ℝ) + 2) ^ (-10 : ℤ) ≤
          coinProb I p (fun w => (cost I (asg I (alg (I, w))) : ℝ) ≤
            A * ((I.n : ℝ) / Real.log ((I.n : ℝ) + 2)) ^ (k - 4) * (OPT I : ℝ))) ∧
    (OptInapprox.MaxCut.UGC →
      (∀ ρ p₀ : ℝ, 0 < p₀ →
        RandApproxOn (fun I => CompleteSigned nae 4 I ∧ 1 ≤ OPT I) (fun _ => ρ) p₀ → NPsubBPP) ∧
      (∀ ρ : ℝ,
        RandApproxExpOn (fun I => CompleteSigned nae 4 I ∧ 1 ≤ OPT I) (fun _ => ρ) → NPsubBPP)) ∧
    (∀ k : ℕ, 5 ≤ k → ∀ ε c : ℝ, 0 < ε → 0 < c →
      (∀ p₀ : ℝ, 0 < p₀ →
        RandApproxOn (fun I => CompleteSigned nae k I ∧ 1 ≤ OPT I)
          (fun I => c * (I.n : ℝ) ^ ((k : ℝ) - 4 - ε)) p₀ → NPeqRP) ∧
      (RandApproxExpOn (fun I => CompleteSigned nae k I ∧ 1 ≤ OPT I)
          (fun I => c * (I.n : ℝ) ^ ((k : ℝ) - 4 - ε)) → NPeqRP)) := by sorry

end AcceptSubcube.Supplement
