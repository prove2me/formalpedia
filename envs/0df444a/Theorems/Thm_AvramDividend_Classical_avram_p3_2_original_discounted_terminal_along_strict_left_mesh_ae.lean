-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_terminal_along_strict_left_mesh_ae
-- name    : AvramDividend.Classical.avram_p3_2_original_discounted_terminal_along_strict_left_mesh_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:09:54.293172+00:00
-- url     : https://prove2.me/theorems/3fa5f5f4-7e45-44cf-b070-b0d4f95f1a66
-- title:
--   Original strictly surviving discounted terminal convergence along physical left meshes
-- statement:
--   For any explicit sequence of original observation times strictly below a fixed positive horizon converging to it, the original spectrally negative Lévy controlled discounted w postpayment reserve converges almost surely, on strict survival, to the actual pre-rightpayment discounted terminal. No equality in law or payment at horizon deletion.
-- source:
--   Compose the fully Accepted P3-2 original discounted terminal left-tendsto theorem with the supplied strict-left mesh convergence into the left neighbourhood filter. The result retains the exact original reserve, cap, right payments and ruin clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_survivor_pre_rightpayment_terminal_left_tendsto_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_discounted_terminal_along_strict_left_mesh_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (q : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < t)
    (huLimit : Tendsto u atTop (𝓝 t)) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ruinTime X x D ω →
      Tendsto (fun n : ℕ =>
        Real.exp (-(q * (u n : ℝ))) *
          w (x + X.X (u n) ω - rightLimit D (u n) ω))
        atTop
        (𝓝 (Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω))) := by sorry
