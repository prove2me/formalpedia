-- Prove2me | Theorems.Thm_EconomicsNextProof_upperMobius_const
-- name    : EconomicsNextProof.upperMobius_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:45.848224+00:00
-- url     : https://prove2.me/theorems/dd4e35cd-174a-4fa5-98f5-249f5bd60bae
-- title:
--   Economics Next Proof: upper Mobius const
-- statement:
--   A constant upper Möbius transform is supported only at the full set.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Mobius.lean#L135-L143
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Mobius.lean#L135-L143

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Mobius
set_option autoImplicit true
@[expose] public section
public section
open EconomicsNextProof
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem EconomicsNextProof.upperMobius_const (c : ℝ) (A : Finset X) :
    upperMobius (fun _ => c) A = if A = Finset.univ then c else 0 := by sorry
