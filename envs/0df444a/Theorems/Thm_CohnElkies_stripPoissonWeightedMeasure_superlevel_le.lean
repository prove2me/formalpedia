-- Prove2me | Theorems.Thm_CohnElkies_stripPoissonWeightedMeasure_superlevel_le
-- name    : CohnElkies.stripPoissonWeightedMeasure_superlevel_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/d201cf96-4a78-4e6d-9d5b-fd0620864231
-- title:
--   CohnElkies.stripPoissonWeightedMeasure_superlevel_le
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

theorem CohnElkies.stripPoissonWeightedMeasure_superlevel_le
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} {B t : ℝ}
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (ht : 0 < t) (s : ℝ) :
    stripPoissonWeightedMeasure σ s
        {x : ℝ | t < f x} ≤
      stripPoissonWeightedMeasure σ 0
        {x : ℝ | t < f x} := by sorry
