-- Prove2me | solution 1 for perp_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:06:25.263327+00:00
-- url     : https://prove2.me/submissions/9eeb5839-063f-4d09-96e5-bd30671bb29d

import Mathlib
import Definitions.Def_Basic

set_option autoImplicit true

theorem _root_.solution {P : Type*} [PartialOrder P] (a b : P) :
    (a ⊥ b) ↔ ¬ a ≤ b ∧ ¬ b ≤ a := Iff.rfl
