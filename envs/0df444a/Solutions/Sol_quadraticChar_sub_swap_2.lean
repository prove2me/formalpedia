-- Prove2me | solution 2 for quadraticChar_sub_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:52:27.241714+00:00
-- url     : https://prove2.me/submissions/9121b352-66fb-4964-9957-d452e88e65a9

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament

set_option autoImplicit true
@[expose] public section
public section
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
theorem _root_.solution (hneg : quadraticChar F (-1) = -1) (a b : F) :
    quadraticChar F (a - b) = -quadraticChar F (b - a) := by
  rw [← neg_sub b a, ← neg_one_mul, map_mul, hneg, neg_one_mul]
