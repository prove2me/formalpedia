-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_anycap_arbitrary_cofinal_spatial_lower_and_upper_endpoint_dichotomy_without_mesh_rate
-- name    : AvramDividend.Classical.avram_bva_a22_original_anycap_arbitrary_cofinal_spatial_lower_and_upper_endpoint_dichotomy_without_mesh_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:33:55.440189+00:00
-- url     : https://prove2.me/theorems/f4f20448-845e-4e7b-9062-fe4816550fe4
-- title:
--   Original arbitrary cofinal positive spatial bands exhaust both endpoints for any finite or infinite dividend cap, without a selected mesh rate
-- statement:
--   For every positive original dividend cap, finite or infinite, and all actual arbitrary prescribed spatial cofinal band sequences satisfying the exact half-band interior source conditions, prove the full endpoint dichotomy: lower reserve endpoint converges to zero, finite-cap upper endpoint converges to the true finite cap whenever the cap equals a positive real cap, and infinite-cap upper endpoint escapes every finite reserve. All three claims hold for the same unmodified row sequence and do not presume nested bands, prescribed rates relative to the physical clock, or an adaptively selected fast spatial diagonal. This packages the Proved BVA-A22 source boundary exhaustion results into one reusable joint localisation certificate for the actual original BV stopped C1 positive-error argument. It controls spatial endpoints only and does not itself prove convergence of the original stopped physical Taylor or contact error.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_finitecap_arbitrary_cofinal_spatial_upper_band_tendsto_cap_without_rate
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_infinitecap_arbitrary_cofinal_spatial_upper_band_tendsto_infinity_without_rate
open Classical Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_anycap_arbitrary_cofinal_spatial_lower_and_upper_endpoint_dichotomy_without_mesh_rate
    (C : ℝ≥0∞) (hC : 0 < C) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    Tendsto a atTop (𝓝 (0 : ℝ)) ∧
    (∀ L : ℝ, 0 < L → C = ENNReal.ofReal L →
      Tendsto b atTop (𝓝 L)) ∧
    (C = ⊤ → Tendsto b atTop atTop) := by sorry
