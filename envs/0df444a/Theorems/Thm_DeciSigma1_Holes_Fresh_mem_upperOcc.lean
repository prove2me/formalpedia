-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_upperOcc
-- name    : DeciSigma1.Holes.Fresh.mem_upperOcc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:48.473272+00:00
-- url     : https://prove2.me/theorems/fbf29b20-edb2-4f3e-b886-5e777d4be23c
-- title:
--   Fresh: mem upper Occ
-- statement:
--   The Fresh construction uses the mem upper Occ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L316-L324
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L316-L324

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

theorem DeciSigma1.Holes.Fresh.mem_upperOcc {W : Fin k → List α} {t : ℕ} {o : Fin k × ℕ × ℕ} :
    o ∈ upperOccurrences W t ↔ W o.1 ≠ [] ∧ o.2.2 ∈ anchors W (t + 1) o.1 ∧ o.2.1 =
        upperOccurrenceStart W t o.1 o.2.2 := by sorry
