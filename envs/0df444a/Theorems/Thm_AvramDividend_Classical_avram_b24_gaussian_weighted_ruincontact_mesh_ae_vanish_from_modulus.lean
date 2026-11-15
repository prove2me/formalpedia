-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_gaussian_weighted_ruincontact_mesh_ae_vanish_from_modulus
-- name    : AvramDividend.Classical.avram_b24_gaussian_weighted_ruincontact_mesh_ae_vanish_from_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:57:43.413202+00:00
-- url     : https://prove2.me/theorems/1f6c4562-a562-4197-a058-a1a0dd3d6a41
-- title:
--   Bounded predictable original Gaussian ruin-contact mesh noise vanishes almost surely from continuity
-- statement:
--   For the original intrinsic Gaussian sample source R with a compact-time pathwise continuity modulus, a sequence of separated genuine physical grids with vanishing cell size, bounded real predictable weights WG, and the strict-left inclusive-right ruin-contact mask, the entire weighted Gaussian noise crossing cell converges almost surely to zero. This is a direct weighted version of the Proved unique-contact norm bound; no independence from the stopping time is assumed and the pre-ruin right-payment cash remains separate. The original finite-activity Gaussian source continuity theorem supplies the modulus.
-- source:
--   Proved B24 last contact single-cell norm bound and bounded weight norm multiplication on original source.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_single_ruincontact_mesh_sum_norm_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_gaussian_weighted_ruincontact_mesh_ae_vanish_from_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (R : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (T : ℝ≥0)
    (S : ℕ → Finset ℕ) (a b : ℕ → ℕ → ℝ≥0)
    (WG : ℕ → ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hSep : ∀ k i j, i ∈ S k → j ∈ S k → i < j → b k i ≤ a k j)
    (hOrdered : ∀ k i, i ∈ S k → a k i ≤ b k i)
    (hT : ∀ k i, i ∈ S k → b k i ≤ T)
    (hWeights : ∀ k i, i ∈ S k → ∀ ω, ‖WG k i ω‖ ≤ L)
    (hGridSmall : ∀ δ : ℝ≥0, 0 < δ →
      ∃ K : ℕ, ∀ k, K ≤ k → ∀ i ∈ S k, b k i - a k i ≤ δ)
    (hMod : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → t - s ≤ δ →
        ‖R t ω - R s ω‖ ≤ ε) :
    ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ =>
        ((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
          (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω)))
      atTop (𝓝 (0 : ℝ)) := by sorry
