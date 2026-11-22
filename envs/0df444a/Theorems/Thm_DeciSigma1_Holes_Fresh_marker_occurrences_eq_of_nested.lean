-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_marker_occurrences_eq_of_nested
-- name    : DeciSigma1.Holes.Fresh.marker_occurrences_eq_of_nested
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:00.265804+00:00
-- url     : https://prove2.me/theorems/ad172d88-c7fe-40b8-9b14-5ed538584598
-- title:
--   Fresh: marker occurrences eq of nested
-- statement:
--   An occurrence of an active level-`t` marker inside an occurrence of another one, in any
--   text, is the same occurrence of the same marker text.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L647-L654
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L647-L654

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

theorem DeciSigma1.Holes.Fresh.marker_occurrences_eq_of_nested {t : ℕ} {m m' : Fin k}
    (hm : m ∈ active W t) (hm' : m' ∈ active W t) {u : List α} {i j : ℕ}
    (h : marker W t m <+: u.drop i) (h' : marker W t m' <+: u.drop j) (hij : i ≤ j)
    (hlen : j + (marker W t m').length ≤ i + (marker W t m).length) :
    i = j ∧ marker W t m' = marker W t m := by sorry
