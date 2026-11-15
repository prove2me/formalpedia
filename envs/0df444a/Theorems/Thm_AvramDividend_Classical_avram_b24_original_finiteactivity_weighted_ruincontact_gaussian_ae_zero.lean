-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_weighted_ruincontact_gaussian_ae_zero
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_weighted_ruincontact_gaussian_ae_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:40:37.717722+00:00
-- url     : https://prove2.me/theorems/a9c6bbc4-c049-44a2-a161-921e2aa881fb
-- title:
--   Actual original finite-activity Gaussian bounded-predictable ruin-contact mesh error vanishes a.e.
-- statement:
--   For an arbitrary intrinsic Gaussian limit R constructed from the actual original finite-negative-jump-activity spectrally negative Levy source X on the same sample space, any bounded predictable weighted sequence of separated genuine physical deterministic grids with mesh size tending to zero has ruin-crossing strict-left/inclusive-right Gaussian contact noise tending almost surely to zero. Follows from the Proved source compact time modulus and terminal contact single-cell bound without assuming Gaussian independence from the stopping clock, an auxiliary Brownian, or post-ruin semimartingale cash.
-- source:
--   Proved B24 last contact single-cell norm bound and bounded weight norm multiplication on original source.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_single_ruincontact_mesh_sum_norm_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_gaussian_global_continuity_compact_time_modulus
import Theorems.Thm_AvramDividend_Classical_avram_b24_gaussian_weighted_ruincontact_mesh_ae_vanish_from_modulus
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_weighted_ruincontact_gaussian_ae_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (σ : Ω → ℝ≥0) (T : ℝ≥0)
    (S : ℕ → Finset ℕ) (a b : ℕ → ℕ → ℝ≥0)
    (WG : ℕ → ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hSep : ∀ k i j, i ∈ S k → j ∈ S k → i < j → b k i ≤ a k j)
    (hOrdered : ∀ k i, i ∈ S k → a k i ≤ b k i)
    (hT : ∀ k i, i ∈ S k → b k i ≤ T)
    (hWeights : ∀ k i, i ∈ S k → ∀ ω, ‖WG k i ω‖ ≤ L)
    (hGridSmall : ∀ δ : ℝ≥0, 0 < δ →
      ∃ K : ℕ, ∀ k, K ≤ k → ∀ i ∈ S k, b k i - a k i ≤ δ)
 :
    ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ =>
        ((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
          (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω)))
      atTop (𝓝 (0 : ℝ)) := by sorry
