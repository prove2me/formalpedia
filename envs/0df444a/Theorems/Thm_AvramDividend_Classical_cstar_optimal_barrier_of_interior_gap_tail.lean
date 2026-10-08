-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier_of_interior_gap_tail
-- name    : AvramDividend.Classical.cstar_optimal_barrier_of_interior_gap_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T15:31:49.50539+00:00
-- url     : https://prove2.me/theorems/d74d5173-f700-48c7-9f26-d8bfef30eeee
-- title:
--   Best dividend barrier from scale-function monotonicity, derivative tail condition, and regularity
-- statement:
--   Given the canonical IsScaleFunction X q W, derivative continuity on [0,infinity), a positive interior derivative improvement over the value at zero with an eventual tail lower bound, positive derivative at the infimum-defined cstar, a zero-boundary denominator comparison, and interior differentiability, prove cstar finite and the canonical barrier optimal among competing barriers for x in [0,cstar]. Nonnegativity and continuity of W itself are derived from IsScaleFunction, and cstar minimum attainment is derived rather than assumed. This is a conditional direct bridge to Proposition 3(i), not yet a proof of the unconditional mission theorem.
-- source:
--   Compose conditional cstar_finite_attained_of_interior_gap_and_tail with cstar_barrier_compare_of_attained_positive_minimal. Both W>=0 and ContinuousOn W (Icc 0 cstar) are projections of IsScaleFunction and restriction of its continuity on Ici 0. Remaining analytic inputs are explicitly marked rather than smuggled in from Standing.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem cstar_optimal_barrier_of_interior_gap_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hcontDeriv : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (a : ℝ) (ha : 0 < a) (hgap : deriv W a < deriv W 0)
    (htail : ∀ᶠ x : ℝ in Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici (0 : ℝ)),
      deriv W a ≤ deriv W x)
    (hpositive : 0 < deriv W (cstar W).toReal)
    (hboundary : scaleDeriv W 0 = ⊤ ∨
      (scaleDeriv W 0).toReal = 0 ∨
      deriv W (cstar W).toReal ≤ (scaleDeriv W 0).toReal)
    (hdiff : DifferentiableOn ℝ W (Set.Ioo 0 (cstar W).toReal)) :
    cstar W < ⊤ ∧ ∀ x b : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ b →
      barrierValue W b x ≤ vcstar W x := by
  sorry

end AvramDividend.Classical
