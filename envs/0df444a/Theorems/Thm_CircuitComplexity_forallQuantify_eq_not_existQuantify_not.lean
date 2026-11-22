-- Prove2me | Theorems.Thm_CircuitComplexity_forallQuantify_eq_not_existQuantify_not
-- name    : CircuitComplexity.forallQuantify_eq_not_existQuantify_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:01.034187+00:00
-- url     : https://prove2.me/theorems/88ed6b4a-879e-4fed-8cf7-47d45b440ff8
-- title:
--   Circuit Complexity: forall Quantify eq not exist Quantify not
-- statement:
--   De Morgan duality: universal quantification equals negated existential
--       of negation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism/Defs.lean#L67-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism/Defs.lean#L67-L72

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}

theorem CircuitComplexity.forallQuantify_eq_not_existQuantify_not
    (f : BitString (k + m) → Bool) (y : BitString m) :
    forallQuantify f y = !(existQuantify (fun z => !(f z)) y) := by sorry
