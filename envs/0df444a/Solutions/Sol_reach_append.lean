-- Prove2me | solution 1 for reach_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:47:39.89081+00:00
-- url     : https://prove2.me/submissions/3d71e372-ceed-4a7d-900a-a8c485e93690

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace

set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
local infixr:60 " ≈ₜ " => TraceEquiv R
theorem _root_.solution {L : Type*} (F : ConfFamily L) (c : Set F.Event) (t p : List F.Event) :
    reach F (reach F c t) p = reach F c (t ++ p) := by
  ext x; simp [reach]; tauto
