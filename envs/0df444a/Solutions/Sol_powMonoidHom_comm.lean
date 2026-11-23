-- Prove2me | solution 1 for powMonoidHom_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:58.720642+00:00
-- url     : https://prove2.me/submissions/76bbae1c-47b1-46e5-9cad-ffdc2f4e6c0e

import Mathlib.Algebra.Group.Hom.Basic
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Hom_Basic

set_option autoImplicit false

theorem _root_.solution {α : Type*} {β : Type*} {n : ℕ} [CommMonoid α] [CommMonoid β] {f : α →* β} :
    (powMonoidHom n).comp f = f.comp (powMonoidHom n) := by
  ext; simp
