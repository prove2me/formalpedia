-- Prove2me | Theorems.Thm_EconomicsNextProof_upperSum_upperMobius
-- name    : EconomicsNextProof.upperSum_upperMobius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:27.643213+00:00
-- url     : https://prove2.me/theorems/793fabd0-eb8a-54b2-873b-06aee5fca1a0
-- title:
--   Economics Next Proof: upper Sum upper Mobius
-- statement:
--   The upper subset sum and its Möbius transform are two-sided inverses.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Mobius.lean#L123-L132
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Mobius.lean#L123-L132

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

theorem EconomicsNextProof.upperSum_upperMobius (f : Finset X → ℝ) : upperSum (upperMobius f) = f := by sorry
