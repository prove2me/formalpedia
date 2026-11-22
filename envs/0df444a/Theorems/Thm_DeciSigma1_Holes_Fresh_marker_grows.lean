-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_marker_grows
-- name    : DeciSigma1.Holes.Fresh.marker_grows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:33.737796+00:00
-- url     : https://prove2.me/theorems/73ff00f9-93ef-4e3f-b92f-5b85771665c9
-- title:
--   Fresh: marker grows
-- statement:
--   The marker of a coordinate that stays active grows strictly.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L528-L532
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L528-L532

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

theorem DeciSigma1.Holes.Fresh.marker_grows {t : ℕ} {l : Fin k} (hl : l ∈ active W (t + 1)) :
    (marker W t l).length < (marker W (t + 1) l).length := by sorry
