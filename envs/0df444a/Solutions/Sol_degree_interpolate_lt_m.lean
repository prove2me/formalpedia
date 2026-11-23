-- Prove2me | solution 1 for degree_interpolate_lt_m
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:20:18.500504+00:00
-- url     : https://prove2.me/submissions/f7c9f5ac-2ef2-4c04-bf90-461670e0597f

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_card_block_le_m

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ)
    (hm : m > 0) (f : F → F) (z : F) :
    (Lagrange.interpolate (Block D m z) id f).degree < m :=
  (Lagrange.degree_interpolate_lt f (Set.injOn_id _)).trans_le
    (Nat.cast_le.mpr (card_block_le_m D m z hm))
