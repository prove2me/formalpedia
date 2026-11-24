-- Prove2me | solution 1 for quadraticChar_sub_swap
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:03.863462+00:00
-- url     : https://prove2.me/submissions/ec8a216b-8297-4921-aa6a-e7408a12ff1c

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


theorem solution (hneg : quadraticChar F (-1) = -1) (a b : F) :
    quadraticChar F (a - b) = -quadraticChar F (b - a) := by
  rw [show a - b = (-1) * (b - a) by ring, map_mul,hneg,neg_one_mul]
