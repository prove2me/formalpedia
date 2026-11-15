-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_intrinsic_marked_mesh_weight_perturbation_L1_variation_bound
-- name    : AvramDividend.Classical.avram_b24_original_intrinsic_marked_mesh_weight_perturbation_L1_variation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:53:37.36281+00:00
-- url     : https://prove2.me/theorems/b4e40021-4728-4f5e-a7fb-2b1968e8f07b
-- title:
--   Actual original compensated-mark finite physical mesh gain is Lipschitz in bounded predictable coefficient perturbations in L1
-- statement:
--   For any true same-space finite-negative-activity intrinsic compensated small-negative mark source Jsmall, a finite physical grid with original endpoints, and two bounded predictable coefficient systems WG,WJ differing by at most ε at every original cell and sample path, the L1 difference between their finite marked stochastic integral gains is at most ε times the expected genuine total variation bound V of the source on the grid. This is a rigorous original noise continuity estimate that can be used on common refinements of stopped physical Itô-Meyer meshes to establish L1 Cauchy once C² pre-left gradient coefficients converge. It retains true negative ruin-contact jumps and requires no large-negative-jump moments, surrogate Poisson processes or postruin extension.
-- source:
--   Pinned finite norm triangle, bounded predictable coefficient difference and Bochner integral inequality, original intrinsic Jsmall source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_intrinsic_marked_mesh_weight_perturbation_L1_variation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (WG WJ : ℕ → Ω → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hClose : ∀ i ∈ S, ∀ ω, ‖WG i ω - WJ i ω‖ ≤ ε)
    (hMeshI : Integrable (fun ω =>
      ∑ i ∈ S, (WG i ω - WJ i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)) P)
    (hVarI : Integrable (fun ω => ∑ i ∈ S,
      ‖Jsmall (b i) ω - Jsmall (a i) ω‖) P)
    (V : ℝ) (hV : 0 ≤ V)
    (hVarMean : (∫ ω, ∑ i ∈ S,
      ‖Jsmall (b i) ω - Jsmall (a i) ω‖ ∂P) ≤ V) :
    (∫ ω, ‖∑ i ∈ S, (WG i ω - WJ i ω) *
      (Jsmall (b i) ω - Jsmall (a i) ω)‖ ∂P) ≤ ε * V := by sorry
