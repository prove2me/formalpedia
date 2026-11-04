-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_infinite_cap_discounted_terminal_nonnegative
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_infinite_cap_discounted_terminal_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:39:11.216405+00:00
-- url     : https://prove2.me/theorems/d67035c5-439d-4ba6-bff4-cc4b495a2bcd
-- title:
--   Exact original infinite-cap discounted stopped terminal is pathwise nonnegative
-- statement:
--   For the genuine source W at its right-limit dividend or ruin reserve and exact discounted terminal, canonical C=∞ implies global w≥0 via the separately accepted infinite-cap interior-gradient boundary lemma. The exponential discount is positive, so Term≥0 on every original sample path. This is a source-grounded Fatou/localisation premise and does not assume stochastic integrability or a new process.
-- source:
--   P4-F original infinite-cap candidate nonnegative helper, original exact W/Term definitions, Mathlib Real.exp_pos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_infinite_cap_candidate_nonnegative
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_infinite_cap_discounted_terminal_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hCtop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ ω, 0 ≤ Term ω := by sorry
