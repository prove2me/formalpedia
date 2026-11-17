-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_5
-- name    : DeepQOperator.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:42:59.747204+00:00
-- url     : https://prove2.me/theorems/580c4d26-f3cc-4c4a-85cc-8310ed4cb41c
-- title:
--   Theorem 5, p.7 — two adaptive affine queries cost at least $2^{-52}\gamma$ on the envelope family
-- statement:
--   For every $m\ge2$ and every $\gamma>0$, every measurable randomized adaptive algorithm that makes at most two arbitrary affine queries on every input and random path satisfies, on the envelope family (13)–(14),
--   $$
--   \sup_{\theta\in[0,m+1]\times[0,1]^m}\mathbb{E}_\omega\,\ell\big(A(\theta;\omega),\theta\big)\ \ge\ 2^{-52}\gamma. \tag{18}
--   $$
--   Consequently, the exact adaptive query complexity of the envelope family is three, for both arbitrary affine and raw information: three raw queries give zero regret.
--
--   The bound also holds after any quantization of the replies. Common positive response mixing with weight $0<\lambda<1$ multiplies it by $1-\lambda$.
--
--   This is the adaptive lower bound matching the three-query algorithm of Theorem 4, and it holds even for the stronger arbitrary-affine oracle.
--
--   Differences from the source:
--   - encoding: worst-input expected regret $\sup_\theta E_\omega \ell(A(\theta;\omega),\theta)$ → an $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued supremum of lower Lebesgue integrals of the loss; reason: Lean convention; the loss is nonnegative and bounded, so the values agree
--   - encoding: at most $N$ queries (reply bits) on every input and random path → the algorithm is run with fuel $N$ (protocols: hard budget `HardBudgetOn` and fuel $B$); reason: a run with fuel $N$ asks at most $N$ queries, and an algorithm with hard budget $N$ behaves identically under fuel $N$
--   - encoding: randomized algorithm with private seed; deterministic algorithm → seed space a standard Borel probability space $(\Omega,\mu)$; deterministic = seed space `Unit` with the Dirac measure; reason: the standing randomization model (20), §5, p.8
--   - encoding: after any quantization of the replies → the algorithm observes $q(\text{reply})$ for an arbitrary jointly measurable real-valued observation map $q$ (seed and history dependent); reason: every standard Borel alphabet embeds measurably into $\mathbb{R}$
--   - reading: common positive response mixing multiplies the bound by $1-\lambda$ → for every $\lambda\in(0,1)$ the mixed family, built from the mixed Bellman scores (1), has worst regret at least $(1-\lambda)$ times the constant, for quantized algorithms as well; reason: mixing multiplies every loss by $1-\lambda$ and leaves the observations unchanged (p.10), so the scaled bound holds for every algorithm the unmixed bound covers
--   - reading: exact adaptive query complexity is three for both affine and raw information → a deterministic three-query raw algorithm with zero worst regret, together with the two-query lower bound (18); reason: raw queries are affine, so the two-query affine bound covers raw algorithms
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 5 and eq. (18), p.7 (PDF p.10); 'Strict positivity', p.7; proof in Appendix H, pp.32–34

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg
import Definitions.Def_DeepQOperator_Supplement_Envelope

open MeasureTheory

namespace DeepQOperator.Supplement

/-- **Theorem 5 (Sharp adaptive affine-query complexity)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy
Adaptive Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256
9f8f3285…), Theorem 5, p.7, PDF p.10; proved in Appendix H, pp.32–34).

For every `m ≥ 2` and `γ > 0`, every measurable randomized adaptive algorithm making at most two
arbitrary affine queries on every input and random path has
`sup_{θ ∈ [0,m+1]×[0,1]^m} E_ω ℓ(A(θ; ω), θ) ≥ 2^{-52} γ` (18) on the envelope family. Consequently the
exact adaptive query complexity is three for both arbitrary affine and raw information (three raw
queries give zero regret). The bound also holds after any quantization of the replies, and common
positive response mixing with weight `λ ∈ (0,1)` multiplies it by `1 - λ`.

**Formalization Note.** Algorithms are `AdaptiveAlg (EnvCoord m) Ω` on a standard Borel probability
seed space, measurable, run with fuel `2` (the hard budget). "After any quantization": the algorithm
observes `quant ω h (reply)` for an arbitrary jointly measurable real-valued observation map (an
arbitrary standard Borel alphabet embeds measurably in `ℝ`); the exact model is `IsExact`. The mixed
family is built from the mixed Bellman scores (`envLoss m γ λ`), not by rescaling the loss. -/
theorem theorem_5 :
    ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ →
      (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (A : AdaptiveAlg (EnvCoord m) Ω), A.IsExact → A.IsMeasurable →
        ENNReal.ofReal (γ / 2 ^ 52) ≤ algRegret (envBox m) (envLoss m γ 0) μ A 2) ∧
      (∃ A : AdaptiveAlg (EnvCoord m) Unit, A.IsExact ∧ A.IsRaw (envDictionary m) ∧
        A.IsMeasurable ∧ algRegret (envBox m) (envLoss m γ 0) (Measure.dirac ()) A 3 = 0) ∧
      (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (A : AdaptiveAlg (EnvCoord m) Ω), A.IsMeasurable →
        ENNReal.ofReal (γ / 2 ^ 52) ≤ algRegret (envBox m) (envLoss m γ 0) μ A 2) ∧
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (A : AdaptiveAlg (EnvCoord m) Ω), A.IsMeasurable →
        ENNReal.ofReal ((1 - lam) * (γ / 2 ^ 52)) ≤ algRegret (envBox m) (envLoss m γ lam) μ A 2) := by sorry

end DeepQOperator.Supplement
