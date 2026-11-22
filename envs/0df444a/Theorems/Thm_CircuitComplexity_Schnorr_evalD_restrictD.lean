-- Prove2me | Theorems.Thm_CircuitComplexity_Schnorr_evalD_restrictD
-- name    : CircuitComplexity.Schnorr.evalD_restrictD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:18.382808+00:00
-- url     : https://prove2.me/theorems/d38de2da-dc05-4ac7-a11a-1c9f55eb68af
-- title:
--   Schnorr: eval D restrict D
-- statement:
--   The Schnorr construction uses the eval D restrict D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L224-L232
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L224-L232

module
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Schnorr

theorem CircuitComplexity.Schnorr.evalD_restrictD {N s : Nat} (d : CircDesc (N + 1) s)
    (hs : 0 < s) (a : Fin (N + 1)) (b : Bool) (x : BitString N) :
    evalD hs (restrictD d a b) x = evalD hs d (insertAt x a b) := by sorry
