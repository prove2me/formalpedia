-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_marker_occurrences_in_next_marker
-- name    : DeciSigma1.Holes.Fresh.marker_occurrences_in_next_marker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:48.133816+00:00
-- url     : https://prove2.me/theorems/cbd5c51d-353c-48ac-9269-805a98a15c79
-- title:
--   Fresh: marker occurrences in next marker
-- statement:
--   The complete occurrences of level-`t` markers in a marker of level `t + 1` are exactly one
--   prefix occurrence and one suffix occurrence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L564-L586
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L564-L586

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

theorem DeciSigma1.Holes.Fresh.marker_occurrences_in_next_marker {t : ℕ} (ht : 1 ≤ t) {l : Fin k}
    (hl : l ∈ active W (t + 1)) :
    (∃ m ∈ active W t, marker W t m <+: marker W (t + 1) l) ∧
      marker W t l <:+ marker W (t + 1) l ∧
      ∀ h ∈ active W t, ∀ i, marker W t h <+: (marker W (t + 1) l).drop i →
        i = 0 ∨ i + (marker W t h).length = (marker W (t + 1) l).length := by sorry
