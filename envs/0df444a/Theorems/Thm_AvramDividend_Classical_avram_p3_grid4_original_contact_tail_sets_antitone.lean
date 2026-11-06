-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_contact_tail_sets_antitone
-- name    : AvramDividend.Classical.avram_p3_grid4_original_contact_tail_sets_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:40:26.138389+00:00
-- url     : https://prove2.me/theorems/dca3106c-6199-42f1-9cef-94bba2118983
-- title:
--   Original ruin/horizon stopped payment-time contact-tail sets form a decreasing sequence
-- statement:
--   For the actual original X/D ruin/horizon-clamped stopping time, the true paymentTimes set intersected with the shrinking Ioc(tau-T/(m+1),tau) interval decreases with the mesh index m. This is exactly the Antitone s condition needed by pinned Mathlib MeasureTheory.tendsto_measure_iInter_atTop, independently of any false assumption about the horizon or ruin atom.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_contact_tail_sets_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    Antitone (fun m : ℕ =>
      paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ)) := by sorry
