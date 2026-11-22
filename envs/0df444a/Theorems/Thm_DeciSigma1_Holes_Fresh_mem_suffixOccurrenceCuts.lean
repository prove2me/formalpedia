-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_suffixOccurrenceCuts
-- name    : DeciSigma1.Holes.Fresh.mem_suffixOccurrenceCuts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:54.099793+00:00
-- url     : https://prove2.me/theorems/e59d6edc-5f60-452e-a4da-592a03b847cf
-- title:
--   Fresh: mem suffix Occurrence Cuts
-- statement:
--   The Fresh construction uses the mem suffix Occurrence Cuts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L730-L732
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L730-L732

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
open DeciSigma1.Readers.Table
variable {S : Type} [Fintype S] [DecidableEq S]

theorem DeciSigma1.Holes.Fresh.mem_suffixOccurrenceCuts {W : Fin k → List α} {j : Fin k} {z : List α} {b : ℕ} :
    b ∈ suffixOccurrenceCuts W j z ↔ b < (W j).length ∧ (W j).drop b <+: z := by sorry
