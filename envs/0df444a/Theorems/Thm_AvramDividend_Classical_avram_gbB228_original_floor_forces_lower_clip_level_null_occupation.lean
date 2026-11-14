-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB228_original_floor_forces_lower_clip_level_null_occupation
-- name    : AvramDividend.Classical.avram_gbB228_original_floor_forces_lower_clip_level_null_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:11:26.705072+00:00
-- url     : https://prove2.me/theorems/877a08fe-deb0-44fc-a7d2-b81cac75c1ff
-- title:
--   Original positive floor excludes lower prescribed Gaussian clipping level for Lebesgue-a.e. time
-- statement:
--   For the genuine Lévy source and original dividend strategy, suppose the prepayment risk process stays at least δ>0 strictly before a stopping horizon. Since the postpayment reserve equals the risk process for almost every physical time, the stopped physical-time occupation of the prescribed clipping level δ/2 vanishes for every sample path. This discharges the lower fixed cutoff without Gaussian occupation-density machinery.
-- source:
--   Original Gaussian B65 lower prescribed clip boundary: use Proved avram_wave7_18_original_riskProcess_eq_postpayment_reserve_lebesgue_ae plus positive floor hFloor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB228_original_floor_forces_lower_clip_level_null_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ ω : Ω,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = δ / 2} = 0 := by sorry
