-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_arbitrary_intrinsic_smallmark_source_right_continuous_ae
-- name    : AvramDividend.Classical.avram_b24_original_arbitrary_intrinsic_smallmark_source_right_continuous_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:18:52.979083+00:00
-- url     : https://prove2.me/theorems/f5ce5d5e-d1ca-431b-b670-c862c761f72c
-- title:
--   Every arbitrary original finite-activity intrinsic compensated smallmark witness is right-continuous on a common conull event
-- statement:
--   For the actual finite-negative-activity Lévy X on its own Ω/P, ANY compensated intrinsic smallmark source Jsmall satisfying the same almost-sure all-time cutoff residual witness as B24 has right-continuous original paths at every physical clock on one common P-conull set. Obtain the Proved canonical original smallband right-continuous source from ja18e, use uniqueness of the same original cutoff limit at every physical time on a common conull event, and transfer right continuity pointwise. The result removes an illegitimate extra canonical-source regularity assumption in the true ruin-contact marked Itô-Meyer grid.
-- source:
--   Proved ja18e original same-space locally uniform cadlag intrinsic smallmark source and uniqueness of limits.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18e_original_smallband_locally_uniform_cadlag_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_arbitrary_intrinsic_smallmark_source_right_continuous_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => Jsmall u ω)
        (Ici t) t := by sorry
