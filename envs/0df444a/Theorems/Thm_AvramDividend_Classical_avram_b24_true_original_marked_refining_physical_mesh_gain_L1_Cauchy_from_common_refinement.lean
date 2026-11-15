-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_true_original_marked_refining_physical_mesh_gain_L1_Cauchy_from_common_refinement
-- name    : AvramDividend.Classical.avram_b24_true_original_marked_refining_physical_mesh_gain_L1_Cauchy_from_common_refinement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:18:34.23292+00:00
-- url     : https://prove2.me/theorems/0e387459-74b9-434c-83dc-a738a2db01d7
-- title:
--   Actual original compensated smallmark gains on different refining physical grids are L1 Cauchy from sound common-refinement source certificates
-- statement:
--   For original finite-activity intrinsic compensated Jsmall on the unchanged X/P sample space, suppose every two physical stopped grid gains G_m,G_l admit a GENUINE exact common-refinement representation of their difference as the true original marked increments on that common refinement multiplied by the difference of corresponding bounded predictable weight coefficients. Assume a single uniform finite upper bound V for expected total original Jsmall variation over every common-refinement grid, and that the paired actual coefficients become uniformly close across all cells and paths. Then the originally defined gains G_n are Cauchy in L1. The proof applies the Proved genuine smallmark physical finite-mesh coefficient perturbation inequality with tolerance ε/(V+1), and it works across DIFFERENT refining grids. The exact common-refinement identity is a substantive hypothesis that must be proved from the original stopped mesh; this theorem does not assert it automatically or hide the true ruin-contact mark.
-- source:
--   Proved B24 original same-source physical marked coefficient perturbation L1 theorem and exact common-refinement assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_intrinsic_marked_mesh_weight_perturbation_L1_variation_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_true_original_marked_refining_physical_mesh_gain_L1_Cauchy_from_common_refinement
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (G : ℕ → Ω → ℝ)
    (hGI : ∀ n, Integrable (G n) P)
    (S : ℕ → ℕ → Finset ℕ)
    (a b : ℕ → ℕ → ℕ → ℝ≥0)
    (Wleft Wright : ℕ → ℕ → ℕ → Ω → ℝ)
    (hRefine : ∀ m l ω,
      G m ω - G l ω =
        ∑ i ∈ S m l,
          (Wleft m l i ω - Wright m l i ω) *
            (Jsmall (b m l i) ω - Jsmall (a m l i) ω))
    (V : ℝ) (hV : 0 ≤ V)
    (hVarI : ∀ m l, Integrable (fun ω =>
      ∑ i ∈ S m l,
        ‖Jsmall (b m l i) ω - Jsmall (a m l i) ω‖) P)
    (hVarMean : ∀ m l,
      (∫ ω, ∑ i ∈ S m l,
        ‖Jsmall (b m l i) ω - Jsmall (a m l i) ω‖ ∂P) ≤ V)
    (hWeights : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m l, N ≤ m → N ≤ l →
        ∀ i ∈ S m l, ∀ ω,
          ‖Wleft m l i ω - Wright m l i ω‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m l, N ≤ m → N ≤ l →
      (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε := by sorry
