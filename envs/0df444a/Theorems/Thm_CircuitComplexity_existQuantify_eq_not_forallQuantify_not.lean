-- Prove2me | Theorems.Thm_CircuitComplexity_existQuantify_eq_not_forallQuantify_not
-- name    : CircuitComplexity.existQuantify_eq_not_forallQuantify_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:03.68615+00:00
-- url     : https://prove2.me/theorems/1cc82d92-d666-414c-a1b4-d55e41728faa
-- title:
--   Circuit Complexity: exist Quantify eq not forall Quantify not
-- statement:
--   De Morgan duality: existential quantification equals negated universal
--       of negation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism/Defs.lean#L76-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism/Defs.lean#L76-L81

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}

theorem CircuitComplexity.existQuantify_eq_not_forallQuantify_not
    (f : BitString (k + m) → Bool) (y : BitString m) :
    existQuantify f y = !(forallQuantify (fun z => !(f z)) y) := by sorry
