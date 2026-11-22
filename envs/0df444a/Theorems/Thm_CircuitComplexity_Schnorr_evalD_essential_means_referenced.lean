-- Prove2me | Theorems.Thm_CircuitComplexity_Schnorr_evalD_essential_means_referenced
-- name    : CircuitComplexity.Schnorr.evalD_essential_means_referenced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:13.678138+00:00
-- url     : https://prove2.me/theorems/4777ac81-2559-4012-a542-d6a8088109ee
-- title:
--   Schnorr: eval D essential means referenced
-- statement:
--   If evaluation depends on input `a`, some gate references `a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L96-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L96-L106

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

theorem CircuitComplexity.Schnorr.evalD_essential_means_referenced
    {N s : Nat} (d : CircDesc N s) (hs : 0 < s) (a : Fin N)
    (hdep : ∃ x : BitString N, evalD hs d x ≠ evalD hs d (Function.update x a (!x a))) :
    ∃ g : Fin s, (d g).2.1.1.val = a.val ∨ (d g).2.1.2.val = a.val := by sorry
