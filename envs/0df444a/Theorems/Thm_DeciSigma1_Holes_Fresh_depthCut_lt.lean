-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt
-- name    : DeciSigma1.Holes.Fresh.depthCut_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:16.032661+00:00
-- url     : https://prove2.me/theorems/b3ad0002-50c2-41d0-8276-352142024587
-- title:
--   Fresh: depth Cut lt
-- statement:
--   The Fresh construction uses the depth Cut lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L388-L400
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L388-L400

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

theorem DeciSigma1.Holes.Fresh.depthCut_lt {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d : ℕ} (hd : d < lowerBlockCount W t o) :
    depthCut W t o (d + 1) < depthCut W t o d := by sorry
