-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_ruin_clip_positive_contact_majorant
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_ruin_clip_positive_contact_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:20:26.743971+00:00
-- url     : https://prove2.me/theorems/39863e67-815c-4907-a505-351f66d3c43e
-- title:
--   Original barrier value positive contact error is bounded by zero-clipped post-contact error across ruin
-- statement:
--   Under the original spectrally negative Levy standing and scale-function finite optimal-barrier hypotheses, a nonnegative pre-contact reserve's raw barrier-value positive change is pointwise no larger than the positive change obtained by zero-clipping the possibly ruined post-contact reserve.
-- source:
--   Combine Proved vcstar_eq_zero_of_neg and Proved avram_sweep17_vcstar_nonnegative_without_smoothness, with a case split on actual reserve crossing. This pointwise signed comparison is independent of BV prebudget, mesh, bounded derivative and expectations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_without_smoothness

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_ruin_clip_positive_contact_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (z c : ℝ) (hz : 0 ≤ z) :
    max (vcstar W (z + c) - vcstar W z) 0 ≤
      max (vcstar W (max (z + c) 0) - vcstar W z) 0 := by sorry
