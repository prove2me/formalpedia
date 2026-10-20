-- Prove2me | Theorems.Thm_CohnElkies_even_antitone_poisson_lintegral_max
-- name    : CohnElkies.even_antitone_poisson_lintegral_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/8ca24468-73a4-4807-817f-59f0db21c5d6
-- title:
--   CohnElkies.even_antitone_poisson_lintegral_max
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology

theorem CohnElkies.even_antitone_poisson_lintegral_max
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} {B : ℝ}
    (hfmeas : Measurable f)
    (hfnonneg : ∀ x : ℝ, 0 ≤ f x)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (s : ℝ) :
    (∫⁻ x : ℝ,
      ENNReal.ofReal (f x) ∂stripPoissonWeightedMeasure σ s) ≤
      ∫⁻ x : ℝ,
        ENNReal.ofReal (f x) ∂stripPoissonWeightedMeasure σ 0 := by sorry
