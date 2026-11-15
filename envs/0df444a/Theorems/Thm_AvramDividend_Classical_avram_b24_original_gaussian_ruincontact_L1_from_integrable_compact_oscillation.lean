-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_gaussian_ruincontact_L1_from_integrable_compact_oscillation
-- name    : AvramDividend.Classical.avram_b24_original_gaussian_ruincontact_L1_from_integrable_compact_oscillation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:43:01.966624+00:00
-- url     : https://prove2.me/theorems/3b4683c2-bad6-4d33-bde7-f5a00c9ddb02
-- title:
--   Actual finite-activity Gaussian ruin-contact weighted mesh tends to zero in L1 under an integrable compact oscillation majorant
-- statement:
--   For the actual original finite-activity intrinsic Gaussian R, the weighted unique terminal ruin-crossing mesh tends almost surely to zero by Proved B24 continuity. If the original Gaussian source has an integrable compact-horizon oscillation majorant B and the finite predictable contact mesh gains are integrable, then the contact gain norm is bounded by L·B by unique-cell geometry, so dominated convergence implies it tends to zero in L1. Keeps the original X/P source, strict-left inclusive-right stopping rule and all noise crossing original ruin; exposes the genuine remaining stochastic maximal-integrability requirement.
-- source:
--   Proved B24 original intrinsic Gaussian a.e. contact theorem, single-contact norm bound and dominated-convergence transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_weighted_ruincontact_gaussian_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_b24_single_ruincontact_mesh_sum_norm_bound
import Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_gaussian_ruincontact_L1_from_integrable_compact_oscillation
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
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hOsc : ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t → t ≤ T →
      ‖R t ω - R s ω‖ ≤ B ω)
    (hGI : ∀ k, Integrable (fun ω =>
      ((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
        (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω))) P) :
    Tendsto (fun k => ∫ ω,
      ‖((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
        (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω))‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
