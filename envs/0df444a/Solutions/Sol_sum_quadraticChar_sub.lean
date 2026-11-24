-- Prove2me | solution 1 for sum_quadraticChar_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:56:18.526947+00:00
-- url     : https://prove2.me/submissions/99c93472-64d1-41c2-ad48-a4cc2eab50a1

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
theorem _root_.solution (hF : ringChar F ≠ 2) (a : F) :
    ∑ z : F, quadraticChar F (z - a) = 0 := by
  rw [← quadraticChar_sum_zero hF]
  exact Fintype.sum_equiv (Equiv.subRight a) _ _ fun _ ↦ rfl
