-- Prove2me | solution 1 for isUnit_intCast_of_natAbs_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:46:03.716181+00:00
-- url     : https://prove2.me/submissions/033ecbed-9a9e-4e52-8486-b382ce9209ea

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Theorems.Thm_HasPolychromColouring_neg__f341ff
import Theorems.Thm_IsPolychrom_neg
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ



set_option autoImplicit true
open Finset Pointwise
theorem _root_.solution {n : ℕ} {b : ℤ}
    (h : Nat.gcd b.natAbs n = 1) :
    IsUnit (Int.cast b : ZMod n) := by
  have hu : IsUnit (b.natAbs : ZMod n) := (ZMod.isUnit_iff_coprime _ _).mpr h
  rcases Int.natAbs_eq b with hb | hb <;> rw [hb] <;>
    simp only [Int.cast_natCast, Int.cast_neg] <;> first | exact hu | exact hu.neg
