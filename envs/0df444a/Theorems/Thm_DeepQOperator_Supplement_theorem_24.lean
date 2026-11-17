-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_24
-- name    : DeepQOperator.Supplement.theorem_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:48:40.621536+00:00
-- url     : https://prove2.me/theorems/615b7767-40f9-4126-9eb6-62cd01905213
-- title:
--   Theorem 24, p.58 — randomized fixed affine information with a truncated-Gaussian prior
-- statement:
--   For the normalized family (76)–(78), $m\ge2$, $0<\gamma<1$, set
--   $$
--   L_m=\sqrt{2\log\big(2^{16}(m+1)m^2\big)}
--   $$
--   (natural logarithm). Every randomized fixed design of at most $N\le m$ arbitrary affine measurements satisfies
--   $$
--   \mathfrak D^{\mathrm{fixed,aff,ran}}_N\ \ge\ \frac{\gamma(m+1-N)}{512m^2L_m}. \tag{102}
--   $$
--   For $2\le N\le m$ the matching-scale upper bound
--   $$
--   \mathfrak D^{\mathrm{fixed,aff,ran}}_N\ \le\ \frac{\gamma(m+1-N)}{4m^2} \tag{103}
--   $$
--   is attained by a fixed randomized raw-query design. The exact randomized decision complexity is $m+1$ for fixed affine information and $2$ for adaptive affine or raw information. The lower bound allows arbitrary real coefficients and measurable randomized decoders, with no bound on their processing time.
--
--   Differences from the source:
--   - encoding: worst-input expected regret $\sup_\theta E_\omega \ell(A(\theta;\omega),\theta)$ → an $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued supremum of lower Lebesgue integrals of the loss; reason: Lean convention; the loss is nonnegative and bounded, so the values agree
--   - encoding: at most $N$ queries (reply bits) on every input and random path → the algorithm is run with fuel $N$ (protocols: hard budget `HardBudgetOn` and fuel $B$); reason: a run with fuel $N$ asks at most $N$ queries, and an algorithm with hard budget $N$ behaves identically under fuel $N$
--   - encoding: a fixed design of at most $N$ affine measurements → an `ExactDesign` with exactly $N$ rows, zero rows allowed; reason: a zero row is a known constant, so padding to $N$ rows changes nothing
--   - encoding: randomized algorithm with private seed; deterministic algorithm → seed space a standard Borel probability space $(\Omega,\mu)$; deterministic = seed space `Unit` with the Dirac measure; reason: the standing randomization model (20), §5, p.8
--   - encoding: the minimax value is at least $x$ → every algorithm of the class (measurable, on every standard Borel probability seed space) has worst regret at least $x$; reason: an infimum is at least $x$ exactly when every member is
--   - reading: exact randomized complexity $m+1$ fixed affine, $2$ adaptive affine or raw → a design with $m+1$ rows is exact and every measurable design with $\le m$ rows has positive worst regret; a deterministic two-query raw algorithm is exact and every measurable one-query affine algorithm has positive worst regret; reason: exact complexity is two-sided
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 24 and eqs. (102)–(103), p.58 (PDF p.61); proof in Appendix O

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg
import Definitions.Def_DeepQOperator_Supplement_Normalized

open MeasureTheory

namespace DeepQOperator.Supplement

/-- **Theorem 24 (Randomized fixed affine information)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy
Adaptive Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256
9f8f3285…), Theorem 24, p.58, PDF p.61; proved in Appendix O).

For the normalized family (76)–(78), `m ≥ 2`, `0 < γ < 1`, put `L_m = √(2 log(2^16 (m+1) m²))`
(natural logarithm). Every randomized fixed design of at most `N ≤ m` arbitrary affine measurements
satisfies `𝔇^{fixed,aff,ran}_N ≥ γ(m+1-N)/(512 m² L_m)` (102). For `2 ≤ N ≤ m` the matching-scale upper
bound is `𝔇^{fixed,aff,ran}_N ≤ γ(m+1-N)/(4m²)` (103), attained by a fixed randomized raw-query design.
The exact randomized decision complexity is `m + 1` for fixed affine information and `2` for adaptive
affine or raw information. The lower bound allows arbitrary real coefficients and measurable randomized
decoders, with no bound on their processing time.

**Formalization Note.** Fixed designs are measurable `ExactDesign (NCoord m) Ω N` (arbitrary real rows
and offsets, jointly measurable decoder) on a standard Borel probability seed space; "at most `N`" is
`N` rows, zero rows allowed. The upper bound is a raw design attaining (103). Randomized adaptive
algorithms are measurable `AdaptiveAlg` with exact replies run with fuel equal to the budget; the
deterministic two-query algorithm is the one-point-seed case. `log` is `Real.log`. -/
theorem theorem_24 :
    ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
      (∀ N : ℕ, N ≤ m →
        ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (D : ExactDesign (NCoord m) Ω N), D.IsMeasurable →
        ENNReal.ofReal (γ * ((m : ℝ) + 1 - N) /
            (512 * (m : ℝ) ^ 2 *
              Real.sqrt (2 * Real.log ((2 : ℝ) ^ 16 * ((m : ℝ) + 1) * (m : ℝ) ^ 2)))) ≤
          designRegret (nBox m) (nLoss m γ) μ D) ∧
      (∀ N : ℕ, 2 ≤ N → N ≤ m →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
          (_ : IsProbabilityMeasure μ) (D : ExactDesign (NCoord m) Ω N),
          D.IsMeasurable ∧ IsRawDesign (nDictionary m) D ∧
          designRegret (nBox m) (nLoss m γ) μ D ≤
            ENNReal.ofReal (γ * ((m : ℝ) + 1 - N) / (4 * (m : ℝ) ^ 2))) ∧
      -- exact randomized fixed affine complexity `m + 1`: a design with `m + 1` rows is exact
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
          (_ : IsProbabilityMeasure μ) (D : ExactDesign (NCoord m) Ω (m + 1)),
          D.IsMeasurable ∧ designRegret (nBox m) (nLoss m γ) μ D = 0) ∧
      -- and no design with at most `m` rows is exact
      (∀ N : ℕ, N ≤ m → ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (D : ExactDesign (NCoord m) Ω N), D.IsMeasurable →
        0 < designRegret (nBox m) (nLoss m γ) μ D) ∧
      -- exact randomized adaptive complexity `2`, affine and raw
      (∃ A : AdaptiveAlg (NCoord m) Unit, A.IsExact ∧ A.IsRaw (nDictionary m) ∧ A.IsMeasurable ∧
        algRegret (nBox m) (nLoss m γ) (Measure.dirac ()) A 2 = 0) ∧
      (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (A : AdaptiveAlg (NCoord m) Ω), A.IsExact → A.IsMeasurable →
        0 < algRegret (nBox m) (nLoss m γ) μ A 1) := by sorry

end DeepQOperator.Supplement
