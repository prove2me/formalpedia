-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24y_original_finiteactivity_ruincontact_gaussian_L1_vanish
-- name    : AvramDividend.Classical.avram_b24y_original_finiteactivity_ruincontact_gaussian_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:41:57.901265+00:00
-- url     : https://prove2.me/theorems/fcf586dd-8118-4e46-b23a-c0324939440c
-- title:
--   Original bounded-stop actual Gaussian final-contact mesh contribution vanishes in L1 under physical energy domination
-- statement:
--   For the original finite-activity Levy process, the genuinely clipped terminal Gaussian increment on the unique crossing cell tends to zero almost surely on refined physical grids. When the random weighted sum has a common integrable norm envelope and each mesh is integrable, dominated convergence makes its expected absolute value vanish. No post-ruin source and no replacement process are introduced.
-- source:
--   Combine published original finite-activity stopped Gaussian contact-cell AE vanishing theorem with the published dominated convergence L1 lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24y_original_finiteactivity_ruincontact_gaussian_L1_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Filter.Tendsto (fun n : ℕ =>
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

    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      ((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
        (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω)))
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hFI : ∀ k, Integrable (F k) P)
    (hBound : ∀ k, ∀ᵐ ω ∂P, ‖F k ω‖ ≤ B ω) :
    Filter.Tendsto (fun k => ∫ ω, ‖F k ω‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
