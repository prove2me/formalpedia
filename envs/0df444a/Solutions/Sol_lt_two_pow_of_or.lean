-- Prove2me | solution 1 for lt_two_pow_of_or
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:59.212331+00:00
-- url     : https://prove2.me/submissions/ff24239f-0534-40e1-a766-751028cbdba0

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Theory

set_option autoImplicit true
open Finset
theorem _root_.solution {x y n : Nat} (h : x ||| y < 2 ^ n) : x < 2 ^ n := by
  by_contra! hx
  have := h.trans_le hx
  exact this.not_ge Nat.left_le_or
