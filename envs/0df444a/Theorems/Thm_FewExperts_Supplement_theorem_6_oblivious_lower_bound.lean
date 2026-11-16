-- Prove2me | Theorems.Thm_FewExperts_Supplement_theorem_6_oblivious_lower_bound
-- name    : FewExperts.Supplement.theorem_6_oblivious_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:56:43.433686+00:00
-- url     : https://prove2.me/theorems/b7239fe0-88c4-4e3e-b4a2-85114109a459
-- title:
--   Theorem 6 — $\Omega(\min(\log N,T))$ subscriptions are needed against oblivious adversaries
-- statement:
--   Consider prediction with expert advice with $N$ experts and horizon $T$; logarithms are base 2.
--
--   There is a constant $c>0$ with the following property. Let $N,T\ge2$, and let $\mathcal A$ be a randomized online algorithm, with randomness $\omega\sim\mu$ and measurable in $\omega$, that at round $t$ sees $\omega$ and the gains of rounds $1,\dots,t-1$. Suppose $\mathcal A$ has expected regret at most $T/2$ against every oblivious adversary:
--   $$\mathbb E_\omega\Bigl[\max_i\sum_{t=1}^Tg_t^i-\sum_{t=1}^Tg_t^{a_t}\Bigr]\le\frac T2\qquad\text{for every }g\in[0,1]^{T\times N}.$$
--   Then there is a gain array $g\in[0,1]^{T\times N}$ on which
--   $$\mathbb E_\omega\bigl[\,|\{a_1,\dots,a_T\}|\,\bigr]\ge c\cdot\min(\log N,T).$$
--
--   Since every expert played must be subscribed to, the algorithm subscribes to $\Omega(\min(\log N,T))$ distinct experts in expectation on that input. Some dependence on $N$ is therefore unavoidable for low regret, which complements the polylogarithmic upper bound of Theorem 4.
--
--   Differences from the source:
--   - generalization: must subscribe to Ω(min(log N, T)) distinct experts in expectation → the expected number of distinct experts played in rounds 1..T is at least c·min(log₂ N, T); reason: every played expert is subscribed, so the Lean bound implies the printed one; an algorithm predicting mixtures is covered through its sampled version (same expected regret, plays only subscribed experts, p.13)
--   - encoding: any (randomized) algorithm → any probability space (Ω, μ) of type Type* and A : OnlineAlg Ω N measurable in ω for each round and history; reason: every randomized online algorithm draws its randomness once; measurability makes the expectations genuine
--   - encoding: Ω(·) → ∃ c > 0 chosen before N, T and the algorithm; reason: standard reading
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), Theorem 6, p.34 (PDF p.35)

import Mathlib
import Definitions.Def_FewExperts_alpha
import Definitions.Def_FewExperts_Supplement_adaptivePlay

namespace FewExperts.Supplement

open MeasureTheory

/-- **Theorem 6: Ω(min(log N, T)) subscriptions against oblivious adversaries.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Theorem 6, p.34 (PDF 35): "For N, T ≥ 2, any algorithm with expected regret at most
T/2 against every oblivious adversary must subscribe to Ω(min(log N, T)) distinct experts in
expectation on some input."

There is a constant `c > 0` such that for all `N, T ≥ 2`, every randomized online algorithm `A`
(any probability space `(Ω, μ)`, `A` measurable in its randomness) whose expected regret is at most
`T/2` on every gain array `g ∈ [0, 1]^{T × N}` fixed in advance satisfies, on some such gain array,
`E[number of distinct experts played in rounds 1, …, T] ≥ c · min(log N, T)`.

**Formalization Note** Logs are base 2. Every played expert is subscribed, so the lower bound on
the experts played implies the paper's bound on subscriptions; an algorithm predicting mixtures is
covered through its sampled version, which has the same expected regret and plays only subscribed
experts (p.13). -/
theorem theorem_6_oblivious_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ N T : ℕ, 2 ≤ N → 2 ≤ T →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : LimitedSwitching.HighProb.OnlineAlg Ω N),
        (∀ (t : ℕ) (past : Fin (t - 1) → Fin N → ℝ), Measurable (fun ω => A ω t past)) →
        (∀ g : ℕ → Fin N → ℝ, IsGainSeq T g →
          ∫ ω, gainRegret T g (LimitedSwitching.HighProb.play A ω g) ∂μ ≤ (T : ℝ) / 2) →
        ∃ g : ℕ → Fin N → ℝ, IsGainSeq T g ∧
          c * min (lg N) (T : ℝ) ≤
            ∫ ω, (numPlayed T (LimitedSwitching.HighProb.play A ω g) : ℝ) ∂μ := by sorry

end FewExperts.Supplement
