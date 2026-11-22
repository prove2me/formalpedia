-- Prove2me | Theorems.Thm_CircuitComplexity_Schnorr_wireValD_eq_of_unreferenced
-- name    : CircuitComplexity.Schnorr.wireValD_eq_of_unreferenced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:14.269854+00:00
-- url     : https://prove2.me/theorems/b45f98f0-5f06-48cd-bd24-f1b546f47dd7
-- title:
--   Schnorr: wire Val D eq of unreferenced
-- statement:
--   If no gate references input `a`, wire values are unchanged when `a` is modified.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L66-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L66-L93

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

theorem CircuitComplexity.Schnorr.wireValD_eq_of_unreferenced
    {N s : Nat} (d : CircDesc N s) (a : Fin N) (b : Bool)
    (hno : ∀ g : Fin s, (d g).2.1.1.val ≠ a.val ∧ (d g).2.1.2.val ≠ a.val)
    (x : BitString N) (w : Fin (N + s)) (hw : w.val ≠ a.val) :
    wireValD d x w = wireValD d (Function.update x a b) w := by sorry
