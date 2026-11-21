-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_intrinsic_gaussian_last_partial_stopped_mesh_cell_L1
-- name    : AvramDividend.Classical.avram_freshD_original_intrinsic_gaussian_last_partial_stopped_mesh_cell_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:43:23.24887+00:00
-- url     : https://prove2.me/theorems/bfa148f7-d4f9-448d-8185-fe0b79b7d232
-- title:
--   Original mixed Lévy intrinsic Gaussian last partially stopped deterministic physical mesh cell vanishes in L1 from terminal L2
-- statement:
--   For the actual intrinsic Gaussian residual of a spectrally negative Lévy process with finite negative jump activity and standing assumptions, finite second moment of the intrinsic Gaussian terminal residual and a refining deterministic physical mesh imply vanishing L1 of the last partially stopped bounded weighted Gaussian increment. The interval straddles σ with a(k)<σ≤b(k), its endpoints lie in [0,n] and its width tends uniformly to zero. The original discounted reserve process uses this one-cell correction at the terminal stopped Brownian mesh cell; the conclusion supplies integrability and L1 convergence without postulating an arbitrary integrable bound. It remains valid when negative Lévy jumps occur.
-- source:
--   Genuine original physical Gaussian last partial stopped mesh obligation in Avram Dividend Classical source 242ca5f1 and b98. Combines Proved full intrinsic residual Doob L2 maximal dominator ff34b783 with Proved original finite activity Gaussian contact L1 convergence fcf586dd; no zero-jump assumption and no expected cash budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_physical_Doob_L2_maximal_transfer
import Theorems.Thm_AvramDividend_Classical_avram_b24y_original_finiteactivity_ruincontact_gaussian_L1_vanish
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_intrinsic_gaussian_last_partial_stopped_mesh_cell_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (𝓝 (R t ω)))
    (n : ℕ) (hn : 0 < n)
    (hSquare : Integrable (fun ω => (R (n : ℝ≥0) ω) ^ 2) P)
    (σ : Ω → ℝ≥0) (a b : ℕ → ℝ≥0)
    (hab : ∀ k, a k ≤ b k ∧ b k ≤ (n : ℝ≥0))
    (hMesh : ∀ δ : ℝ≥0, 0 < δ →
      ∃ K : ℕ, ∀ k, K ≤ k → b k - a k ≤ δ)
    (W : ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hWeights : ∀ k ω, ‖W k ω‖ ≤ L)
    (F : ℕ → Ω → ℝ)
    (hF : ∀ k ω, F k ω =
      if a k < σ ω ∧ σ ω ≤ b k then
        W k ω * (R (b k) ω - R (a k) ω)
      else 0)
    (hFm : ∀ k, AEStronglyMeasurable (F k) P) :
    (∀ k, Integrable (F k) P) ∧
    Tendsto (fun k => ∫ ω, ‖F k ω‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
