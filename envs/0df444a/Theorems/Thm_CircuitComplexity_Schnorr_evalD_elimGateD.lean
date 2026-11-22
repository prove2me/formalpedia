-- Prove2me | Theorems.Thm_CircuitComplexity_Schnorr_evalD_elimGateD
-- name    : CircuitComplexity.Schnorr.evalD_elimGateD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:18.047591+00:00
-- url     : https://prove2.me/theorems/fbe09377-24ff-47fc-9cb4-a7509caa5b66
-- title:
--   Schnorr: eval D elim Gate D
-- statement:
--   The Schnorr construction uses the eval D elim Gate D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L422-L435
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L422-L435

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

theorem CircuitComplexity.Schnorr.evalD_elimGateD {N s : Nat} (d : CircDesc N (s + 1))
    (hs : 0 < s) (g : Fin (s + 1)) (rd : GateRedirect (N + s))
    (hrd : ∀ x : BitString N,
      wireValD d x ⟨N + g.val, by omega⟩ = match rd with
        | .const c => c
        | .wire w flip => flip.xor (wireValD d x ⟨w.val, by omega⟩))
    (hrd_wire : ∀ w' flip, rd = .wire w' flip → w'.val < N + g.val)
    (hg_not_last : g.val < s) :
    ∀ x, evalD hs (elimGateD d g rd) x = evalD (by omega : 0 < s + 1) d x := by sorry
