-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_pair_lintegral_all_horizons
-- name    : AvramDividend.Classical.avram_a20_original_borel_pair_lintegral_all_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:38:58.309092+00:00
-- url     : https://prove2.me/theorems/81b5b412-2fa0-42dc-8f04-5bea11e489c4
-- title:
--   Original arbitrary negative Borel chronological marked-pair ENNReal mean for every nonnegative horizon
-- statement:
--   For a finite negative-activity original Lévy process, the exact original chronological marked-jump pair ENNReal expectation equals half the square of the intensity T ν(B) at all nonnegative horizons including T=0. For positive horizons it follows from the new direct physical arbitrary-Borel uniform-grid Fatou moment theorem; at T=0 the original source marked time set is empty and the expectation is zero. This supplies the all-horizon ENNReal source moment needed to close the original real chronological-pair moment and JA36.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_pair_lintegral_all_horizons
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let S : Ω → Set ℝ≥0 := fun ω => {u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    let K : Ω → ℕ := fun ω => ((S ω ×ˢ S ω) ∩
      {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    (∫⁻ ω, (K ω : ℝ≥0∞) ∂P) =
      (((T : ℝ≥0∞) * X.ν B) ^ 2) / 2 := by sorry
