-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
-- name    : AvramDividend.Classical.avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:40:10.245896+00:00
-- url     : https://prove2.me/theorems/b473d1e9-c7cd-404f-950e-d1cc9dca5900
-- title:
--   Actual BV jump-removed physical-grid total variation dominated by original integrable source mass
-- statement:
--   For every original BV Lévy path outside one null set and every sample-dependent nondecreasing physical finite grid from zero to T, the true raw-negative-jump-removed Y has total absolute grid variation at most |drift| T + |T drift − X_T|. The proof starts with the Proved original Y-variation estimate, uses the nonnegative actual raw negative jump sum J_T, and removes the nondecreasing residual R_T. The right-hand side is the original P-integrable envelope of BV-ERROR7 first-moment child (at T ≤ 1). This provides the explicit original stochastic domination budget for Taylor errors with bounded C1 derivative, without importing a signed cash or HJB prebudget.
-- source:
--   Proved original Y physical finite-grid variation 26250e74-0a1e-4cb5-8b80-e748e7bde5d0; original raw jump sum sign 017d744a-d8a5-4239-a5df-4d2243aa2a55; process X.X_zero. BV-ERROR7 L1 mass child 09287ead-652a-4521-8a54-ac198d1c917b; no dependency on it in this pathwise theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_BV_all_Y_physical_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      u 0 = 0 → u n = T →
      (∀ i, i < n → u i ≤ u (i + 1)) →
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       (∑ i ∈ Finset.range n,
         |Y (u (i + 1)) - Y (u i)|) ≤
          |X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|) := by sorry
