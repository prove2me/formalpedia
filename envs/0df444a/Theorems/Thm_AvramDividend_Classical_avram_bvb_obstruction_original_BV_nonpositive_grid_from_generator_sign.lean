-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_BV_nonpositive_grid_from_generator_sign
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_BV_nonpositive_grid_from_generator_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:35:34.825841+00:00
-- url     : https://prove2.me/theorems/0524062b-0a2e-400f-b559-0afc8fee1501
-- title:
--   Original bounded-variation physical B grids are nonpositive a.e. whenever the exact generator grids are nonpositive
-- statement:
--   For any original standing bounded-variation spectrally negative Lévy process and exact physical B, G and stopped drift remainder R definitions, if the generator grid G is nonpositive at every mesh, then the full original BV residual grid B is nonpositive almost surely for all meshes. This is the main auxiliary route to the hAllB premise in the finite-cap original zero-mark pathwise cash theorem.
-- source:
--   Existing Proved fcbb3610 gives B=G a.e. simultaneously at all mesh indices. Apply hG and transport the nonpositive sign pointwise under the same full-probability event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb46_original_all_BV_residual_grid_B_equals_true_generator_G_ae
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_BV_nonpositive_grid_from_generator_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ t ω,
      R t ω = ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0))
    (coeff : ℕ → ℕ → Ω → ℝ)
    (B G : ℕ → Ω → ℝ)
    (hB : ∀ n ω, B n ω = G n ω +
      (∑ i ∈ Finset.range (n + 1),
        coeff n i ω * (R (u n i) ω - R (u n (i + 1)) ω)))
    (hG : ∀ n ω, G n ω ≤ 0) :
    ∀ᵐ ω ∂P, ∀ n, B n ω ≤ 0 := by sorry
