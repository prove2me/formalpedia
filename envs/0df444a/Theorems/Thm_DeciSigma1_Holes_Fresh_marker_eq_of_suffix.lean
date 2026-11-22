-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_marker_eq_of_suffix
-- name    : DeciSigma1.Holes.Fresh.marker_eq_of_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:57.037793+00:00
-- url     : https://prove2.me/theorems/24aafc58-b12f-4881-b636-c0e09ccb3d8f
-- title:
--   Fresh: marker eq of suffix
-- statement:
--   Markers of one level ending at one cut have the same text.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L513-L518
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L513-L518

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

theorem DeciSigma1.Holes.Fresh.marker_eq_of_suffix {t : ℕ} {m m' : Fin k}
    (hm : m ∈ active W t) (hm' : m' ∈ active W t) {u : List α} (h : marker W t m <:+ u)
    (h' : marker W t m' <:+ u) : marker W t m = marker W t m' := by sorry
