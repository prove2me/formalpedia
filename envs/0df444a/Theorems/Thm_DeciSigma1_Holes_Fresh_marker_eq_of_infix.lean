-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_marker_eq_of_infix
-- name    : DeciSigma1.Holes.Fresh.marker_eq_of_infix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:31.076809+00:00
-- url     : https://prove2.me/theorems/eae2f9fd-d0d6-4d75-af69-332811b9c018
-- title:
--   Fresh: marker eq of infix
-- statement:
--   Active markers of one level are never proper factors of each other.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L501-L505
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L501-L505

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
variable {W : Fin k → List α}

theorem DeciSigma1.Holes.Fresh.marker_eq_of_infix (t : ℕ) (m m' : Fin k) (hm : m ∈ active W t)
    (hm' : m' ∈ active W t) : marker W t m <:+: marker W t m' → marker W t m = marker W t m' := by sorry
