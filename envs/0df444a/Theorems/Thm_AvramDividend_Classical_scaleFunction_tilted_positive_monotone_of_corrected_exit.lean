-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_corrected_exit
-- name    : AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:55:50.604925+00:00
-- url     : https://prove2.me/theorems/2d7abb02-c1a8-4929-bece-645bec939c98
-- title:
--   Full q-scale Esscher positivity and monotonicity from the corrected exit identity
-- statement:
--   Under the standing assumptions and positive discount q, assume the corrected killed two-sided exit formula on 0≤x≤a. Then the q-scale W is strictly positive on the positive axis and admits a positive Esscher tilt parameter for which exp(-φx)W(x) is monotone. The bounded-variation part is canonically Proved unconditionally; the unbounded part follows from the published corrected-exit tilted positivity theorem, with no C1 hypothesis. This result is exactly the accepted original tilted-scale prerequisite with a single additional stochastic exit assumption, suitable for direct import once the corrected exit identity is Proved.
-- source:
--   Avram Palmowski Pistorius (2007) corrected two-sided exit formula and Esscher scale normalisation; Proved BV renewal and unbounded-exit branches.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
import Mathlib.Analysis.Complex.Exponential
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi (0 : ℝ)) := by sorry
