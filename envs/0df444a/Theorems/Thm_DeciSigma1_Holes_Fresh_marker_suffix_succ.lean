-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_marker_suffix_succ
-- name    : DeciSigma1.Holes.Fresh.marker_suffix_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:46.721792+00:00
-- url     : https://prove2.me/theorems/6cfd5e87-9dc1-459f-a6ca-98a912708417
-- title:
--   Fresh: marker suffix succ
-- statement:
--   Each next marker has the current marker of its word as a proper suffix.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L521-L525
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L521-L525

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

theorem DeciSigma1.Holes.Fresh.marker_suffix_succ {t : ℕ} {l : Fin k}
    (hl : l ∈ active W (t + 1)) : marker W t l <:+ marker W (t + 1) l := by sorry
