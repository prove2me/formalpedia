-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_finitecap_integrable_discounted_localtime_mean_nonpos
-- name    : AvramDividend.Classical.avram_jump6_B_original_finitecap_integrable_discounted_localtime_mean_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:38:41.607364+00:00
-- url     : https://prove2.me/theorems/275a7f38-c576-456b-beda-3d6eb54d2517
-- title:
--   Original finitecap integrable discounted kink localtime has nonpositive expectation
-- statement:
--   For any original finitecap barrier-source smooth w with subcap derivative at least one, nonnegative localtime occupation L and nonnegative discount weights E yield an integrable finite physical-grid kink correction whose expectation is nonpositive. This aggregates the source-correct nonpositive Tanaka localtime contributions under explicit integrability, without any finite negative-jump activity assumption. The stochastic task is to establish hI for the genuine source masses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB47_original_finitecap_discounted_kink_localtime_correction_nonpositive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_finitecap_integrable_discounted_localtime_mean_nonpos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (S : Finset ℕ) (j : ℕ → ℕ)
    (L E : ℕ → Ω → ℝ)
    (hL : ∀ ω i, i ∈ S → 0 ≤ L i ω)
    (hE : ∀ ω i, i ∈ S → 0 ≤ E i ω)
    (hI : Integrable
      (fun ω => ∑ i ∈ S,
        E i ω * (((1 - deriv w (C.toReal * (((j i + 1 : ℕ) : ℝ) /
          ((j i + 2 : ℕ) : ℝ)))) / 2) * L i ω)) P) :
    (∫ ω, ∑ i ∈ S,
      E i ω * (((1 - deriv w (C.toReal * (((j i + 1 : ℕ) : ℝ) /
        ((j i + 2 : ℕ) : ℝ)))) / 2) * L i ω) ∂P) ≤ 0 := by sorry
