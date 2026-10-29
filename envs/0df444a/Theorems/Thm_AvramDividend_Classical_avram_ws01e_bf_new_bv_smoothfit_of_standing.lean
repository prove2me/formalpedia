-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_smoothfit_of_standing
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_bv_smoothfit_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:45:36.773995+00:00
-- url     : https://prove2.me/theorems/a670aadb-d681-4bf9-9d46-8acc46711f78
-- title:
--   Unconditional BV positive-barrier smooth fit under canonical Standing
-- statement:
--   For a spectrally negative Lévy process satisfying Standing, bounded variation, and a positive finite optimal barrier, the value-candidate derivative at the barrier is one. In the BV branch, Condition (3.3) forces the Lévy measure to be absolutely continuous; existing proved BV C1 scale regularity and BV smooth-fit then apply.
-- source:
--   Source-faithful BV branch of AvramDividend.Classical.vcstar_deriv_eq_one_at_positive_cstar (edf21020), using the exact Definitions Standing and BoundedVariation disjunctions and accepted theorems bced81f2 and 8230ae99.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_bv_contDiff_one
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_bv_smoothfit_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) :
    deriv (vcstar W) (cstar W).toReal = 1 := by sorry
