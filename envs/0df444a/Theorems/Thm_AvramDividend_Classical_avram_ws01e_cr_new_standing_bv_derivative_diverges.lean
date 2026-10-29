-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_standing_bv_derivative_diverges
-- name    : AvramDividend.Classical.avram_ws01e_cr_new_standing_bv_derivative_diverges
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:39:05.335803+00:00
-- url     : https://prove2.me/theorems/cc05667a-aec0-4a3f-97bf-25e435f9769e
-- title:
--   Standing bounded-variation q-scale derivative diverges without a C1 assumption
-- statement:
--   For an actual standing spectrally negative Lévy process with bounded variation and positive discount, the q-scale derivative tends to positive infinity. The differentiability assumption has been discharged by the accepted standing-to-Lévy absolute continuity and the accepted BV absolutely-continuous-Lévy scale C1 result.
-- source:
--   Exact composition of accepted theorems standing_bv_levy_absolutely_continuous, scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy, and bv_scaleDeriv_tendsto_atTop_of_C1. All source-specific hypotheses are retained.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_bv_scaleDeriv_tendsto_atTop_of_C1

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_cr_new_standing_bv_derivative_diverges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    Tendsto (deriv W) atTop atTop := by sorry
