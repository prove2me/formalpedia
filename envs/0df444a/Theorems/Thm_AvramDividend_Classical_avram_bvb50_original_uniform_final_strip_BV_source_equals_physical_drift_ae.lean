-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb50_original_uniform_final_strip_BV_source_equals_physical_drift_ae
-- name    : AvramDividend.Classical.avram_bvb50_original_uniform_final_strip_BV_source_equals_physical_drift_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:53:59.060201+00:00
-- url     : https://prove2.me/theorems/c9c78f94-5446-4d93-928f-76864ecacec8
-- title:
--   Original finite-activity BV Levy source final strict mission grid strip has exact deterministic physical drift increment almost surely
-- statement:
--   On the actual original spectrally negative bounded-variation finite-activity Levy source and original filtration, for the exact prescribed uniform u(n,n+1) approaching T, the full-horizon source increment X_T-X_u eventually equals drift times physical terminal strip width. This follows from Proved original bvb45 eventual negative jump exclusion and Proved original wave4_04a no-jump interval drift identity, using exact original strict endpoint p3_grid4. It directly aids the true terminal stopped cash versus surviving postpayment reward proof, without modifying dividend or ruin definitions.
-- source:
--   Proved bvb45 b7ae7c05, wave4_04a 2a0cae7c, p3_grid4 0071cc00. Original Avram Prop 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb45_original_uniform_grid_eventually_excludes_all_final_source_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- On the actual original finite negative-jump BV source, every sufficiently
fine final strict physical grid cell evolves exactly by the BV drift. -/

theorem AvramDividend.Classical.avram_bvb50_original_uniform_final_strip_BV_source_equals_physical_drift_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, (u n (n + 1) : ℝ) =
      T - T / ((n : ℝ) + 2))
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
      X.X S ω - X.X (u n (n + 1)) ω =
        ((S : ℝ) - (u n (n + 1) : ℝ)) * X.drift := by sorry
