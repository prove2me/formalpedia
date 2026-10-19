-- Prove2me | Theorems.Thm_CohnElkies_even_antitone_superlevel_interval
-- name    : CohnElkies.even_antitone_superlevel_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:53.711061+00:00
-- url     : https://prove2.me/theorems/0c446cb2-5a10-46b7-b093-3158150a6ad3
-- title:
--   CohnElkies.even_antitone_superlevel_interval
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
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology

theorem CohnElkies.even_antitone_superlevel_interval
    {f : ℝ → ℝ} {B t : ℝ}
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (ht : 0 < t) :
    ∃ r : ℝ, 0 ≤ r ∧
      Ioo (-r) r ⊆ {x : ℝ | t < f x} ∧
        {x : ℝ | t < f x} ⊆ Icc (-r) r := by sorry
