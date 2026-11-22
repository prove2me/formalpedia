-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt_of_lt
-- name    : DeciSigma1.Holes.Fresh.depthCut_lt_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:30.872799+00:00
-- url     : https://prove2.me/theorems/bbf7d5ba-5315-496c-8512-0873bf821386
-- title:
--   Fresh: depth Cut lt of lt
-- statement:
--   The Fresh construction uses the depth Cut lt of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L426-L432
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L426-L432

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.depthCut_lt_of_lt {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d d' : ℕ} (hdd : d < d')
    (hd' : d' ≤ lowerBlockCount W t o) : depthCut W t o d' < depthCut W t o d := by sorry
