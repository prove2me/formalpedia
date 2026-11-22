-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_le_length_marker
-- name    : DeciSigma1.Holes.Fresh.le_length_marker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:32.950216+00:00
-- url     : https://prove2.me/theorems/bc8eeea3-b451-4a0c-bcbe-d233f52c4d24
-- title:
--   Fresh: le length marker
-- statement:
--   The Fresh construction uses the le length marker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L534-L541
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L534-L541

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

theorem DeciSigma1.Holes.Fresh.le_length_marker {t : ℕ} {l : Fin k} (hl : l ∈ active W t) :
    t ≤ (marker W t l).length := by sorry
