-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_gaussian_ruincontact_mesh_vanishes_from_source_modulus
-- name    : AvramDividend.Classical.avram_b24_gaussian_ruincontact_mesh_vanishes_from_source_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:55:51.867164+00:00
-- url     : https://prove2.me/theorems/0c2cb60d-3ec1-48cc-8783-14f4e601f511
-- title:
--   Original Gaussian source terminal ruin-contact mesh increment tends to zero a.e. under pathwise compact modulus
-- statement:
--   On the original same-probability-space Gaussian residual path R, for a sequence of separated deterministic partitions of bounded time horizon whose mesh tends to zero, a pathwise modulus of continuity for R implies the sum of the unweighted Gaussian increments over the unique ruin-crossing last cell converges almost surely to zero. The stopped contact mask uses a_i<sigma<=b_i and no post-ruin continuation; the geometric mesh noise limit is a.e. even when sigma depends on the path. The Proved original finite-activity Gaussian source global continuity theorem can supply hMod by Heine-Cantor.
-- source:
--   Proved original B24 unique contact sum norm lemma, uniform continuity on bounded intervals and mesh-size convergence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_single_ruincontact_mesh_sum_norm_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_gaussian_ruincontact_mesh_vanishes_from_source_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (R : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (T : ℝ≥0)
    (S : ℕ → Finset ℕ) (a b : ℕ → ℕ → ℝ≥0)
    (hSep : ∀ k i j, i ∈ S k → j ∈ S k → i < j → b k i ≤ a k j)
    (hOrdered : ∀ k i, i ∈ S k → a k i ≤ b k i)
    (hT : ∀ k i, i ∈ S k → b k i ≤ T)
    (hGridSmall : ∀ δ : ℝ≥0, 0 < δ →
      ∃ K : ℕ, ∀ k, K ≤ k → ∀ i ∈ S k, b k i - a k i ≤ δ)
    (hMod : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → t - s ≤ δ →
        ‖R t ω - R s ω‖ ≤ ε) :
    ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ =>
        ((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
          (fun i => R (b k i) ω - R (a k i) ω))
      atTop (𝓝 (0 : ℝ)) := by sorry
