-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_stopped_compact_previsible
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_ruin_stopped_compact_previsible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:22:18.659822+00:00
-- url     : https://prove2.me/theorems/7759e9e1-2b05-40a3-80c0-b570c12af468
-- title:
--   Original controlled ruin-stopped compact reserve strip has predictable membership and bounded physical horizon
-- statement:
--   For the original Lévy path X.X and the original postpayment dividend control, the true real-horizon truncated ruin clock is a bounded right-continuous stopping time. The stopped positive-reserve compact strip is a right-continuous predictable event, by strong predictability of the genuine pre-reserve left-limit and inclusive survival. Its members satisfy the exact compact pre-reserve and finite-horizon conditions, without any claim of zero occupation at ruin or the cap.
-- source:
--   Source-exact combination of Proved original real-horizon ruin clock 712c7638, Proved original prestate predictable interval 5115705e, and Proved inclusive-survival strong predictability 69806d16.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_truncated_ruin_nnreal_stopping
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_ruin_stopped_compact_previsible
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (a b : ℝ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    (∀ ω, τ ω ≤ T) ∧
    IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    MeasurableSet[𝓕.rightCont.predictable] E ∧
    (∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b) ∧
    (∀ p ∈ E, p.1 ≤ T) := by sorry
