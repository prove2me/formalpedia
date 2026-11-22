-- Prove2me | Theorems.Thm_CircuitComplexity_existQuantify_eq_true
-- name    : CircuitComplexity.existQuantify_eq_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:21.349908+00:00
-- url     : https://prove2.me/theorems/575cee41-489b-4739-a726-20c402ca73b1
-- title:
--   Circuit Complexity: exist Quantify eq true
-- statement:
--   The Circuit Complexity construction uses the exist Quantify eq true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism/Defs.lean#L56-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism/Defs.lean#L56-L58

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}

theorem CircuitComplexity.existQuantify_eq_true {f : BitString (k + m) → Bool} {y : BitString m} :
    existQuantify f y = true ↔ ∃ x : BitString k, f (Fin.append x y) = true := by sorry
