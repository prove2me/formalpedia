-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:37:23.374421+00:00
-- url     : https://prove2.me/theorems/1fdf02a3-3bec-46ad-9b05-10158f2a4189
-- title:
--   Original signed uniform-mesh expectation convergence from measurable source coordinates and measurable test
-- statement:
--   For the actual original spectrally negative Lévy X, a measurable signed test function g bounded by a supported nonnegative f and measurable source fixed-time coordinates imply every exact n+1 grid sum is measurable. Under only the independently supplied a.e. grid-to-genuine-jump-sum convergence hypothesis, prove limit integrability and convergence of actual Bochner expectations. Removes a separate per-grid strong measurability assumption using a published P2-J helper, with no rate or compensator premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_fixed_uniform_mesh_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_signed_grid_measurability_from_path

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 < T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (g : ℝ → ℝ) (hgm : Measurable g)
    (hg : ∀ y, ‖g y‖ₑ ≤ f y)
    (Z : Ω → ℝ)
    (hae : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
           X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω))
      atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n : ℕ => ∫ ω,
          (∑ i ∈ Finset.range (n + 1),
            g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
               X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω)) ∂P)
        atTop (nhds (∫ ω, Z ω ∂P)) := by sorry
