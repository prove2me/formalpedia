-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB129_original_unit_mesh_tube_from_centered_native_brownian
-- name    : AvramDividend.Classical.avram_gbB129_original_unit_mesh_tube_from_centered_native_brownian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:33:38.719314+00:00
-- url     : https://prove2.me/theorems/72065a1e-6c8c-46a9-8363-0c48129f6bb6
-- title:
--   Centred Brownian overshoot tube bounds every original fine-grid Lévy noise endpoint
-- statement:
--   In the original Gaussian Lévy source of drift c=2 represented as X_s=B_s+2s, any centred Brownian path satisfying |B_s|≤1/4000 through s=17/16000 ensures the original uniform unit-horizon grid's centred Lévy source noise remains ≤1/4000 at all points through stopped horizon 1/1000 plus one mesh width, whenever m≥15999. B124 provides Delta_m≤1/16000 and algebra cancels the drift. This is the exact source-tube premise of B121/B122 on the positive event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB124_original_unit_horizon_mesh_step_eventually_below_overshoot
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB129_original_unit_mesh_tube_from_centered_native_brownian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hSource : ∀ u : ℝ≥0, u ≤ (17 / 16000 : ℝ≥0) →
      X.X u ω = B u ω + 2 * (u : ℝ))
    (hc : X.c = 2)
    (hCentered : ∀ u : ℝ≥0, u ≤ (17 / 16000 : ℝ≥0) →
      |B u ω| ≤ (1 / 4000 : ℝ))
    (m : ℕ) (hm : 15999 ≤ m) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    ∀ i : ℕ, s i ≤ (1 / 1000 : ℝ≥0) + Δ →
      |X.X (s i) ω - (s i : ℝ) * X.c| ≤ (1 / 4000 : ℝ)
    := by sorry
