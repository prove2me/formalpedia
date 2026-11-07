-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_compensated_increment_ae_zero
-- name    : AvramDividend.Classical.avram_bv_error7_original_final_contact_compensated_increment_ae_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:14:36.561199+00:00
-- url     : https://prove2.me/theorems/78d4159f-28dd-46ff-9a1c-16b550cf7dbb
-- title:
--   Original Lévy BV compensated increment in the unique final contact cell converges a.e. to zero
-- statement:
--   For the original Lévy process X, the compensated physical BV source Y=X+J has vanishing last-cell increments along a sample-dependent stopped physical grid whenever the genuine Y mesh tends uniformly to zero over the stopped prefix. The zero-clock contact increment is exactly zero.
-- source:
--   The last positive stopped cell has index k-1, hence is among the original refined source cells; use the already provided uniform mesh hypothesis at that index. No dividend-value regularity at ruin/cap is required. Later a uniform bound on the value-change contact cell permits dominated-convergence absorption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_final_contact_compensated_increment_ae_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hMesh : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       ∀ δ : ℝ, 0 < δ → ∀ᶠ m in Filter.atTop,
         ∀ i, i < k m ω →
           |Y (u m (i + 1)) - Y (u m i)| < δ)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun m =>
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
          else 0
        let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
        if k m ω = 0 then (0 : ℝ)
        else Y (u m (k m ω)) - Y (u m (k m ω - 1)))
        atTop (nhds (0 : ℝ)) := by sorry
