-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_true_source_joint_geometric_gaussian_smallmark_centered_ae
-- name    : AvramDividend.Classical.avram_jump6_B_true_source_joint_geometric_gaussian_smallmark_centered_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:30:33.822937+00:00
-- url     : https://prove2.me/theorems/35d03105-43fa-48c3-8751-bbcdf7518eda
-- title:
--   Original coupled Gaussian and small-negative-jump L1 diagonal a.e. zero mean
-- statement:
--   For the actual original probability space, two integrable centred stochastic sources G and J with full L1 Cauchy control, and an error source vanishing in L1, admit one common strictly increasing geometric subsequence. Both source limits converge almost everywhere with integrable dominating envelopes, and retain exactly zero expected martingale contribution, while the error source vanishes almost everywhere. This is the common Gaussian/small-jump localisation and martingale-mean passage required for the infinite-activity stopped source without imposing finite Levy intensity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b25_two_noise_L1_cauchy_geometric_ae_domination
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_dominated_centered_mesh_limit_mean_zero
open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_true_source_joint_geometric_gaussian_smallmark_centered_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G J E : ℕ → Ω → ℝ)
    (hGI : ∀ m, Integrable (G m) P)
    (hJI : ∀ m, Integrable (J m) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hGC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ,
      N ≤ m → N ≤ l → (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε)
    (hJC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ,
      N ≤ m → N ≤ l → (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ε)
    (hEC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ,
      N ≤ m → (∫ ω, ‖E m ω‖ ∂P) ≤ ε)
    (hGcenter : ∀ k, (∫ ω, G k ω ∂ P) = 0)
    (hJcenter : ∀ k, (∫ ω, J k ω ∂ P) = 0) :
    ∃ (K : ℕ → ℕ) (MG MJ BG BJ : Ω → ℝ),
      StrictMono K ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => G (K k) ω) atTop (𝓝 (MG ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => J (K k) ω) atTop (𝓝 (MJ ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => E (K k) ω) atTop (𝓝 (0 : ℝ))) ∧
      Integrable BG P ∧ Integrable BJ P ∧
      (∀ k, ∀ᵐ ω ∂P, ‖G (K k) ω‖ ≤ BG ω) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖J (K k) ω‖ ≤ BJ ω) ∧
      (∫ ω, MG ω ∂ P) = 0 ∧
      (∫ ω, MJ ω ∂ P) = 0 := by sorry
