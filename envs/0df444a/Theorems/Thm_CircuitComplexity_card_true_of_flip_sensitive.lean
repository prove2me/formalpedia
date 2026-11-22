-- Prove2me | Theorems.Thm_CircuitComplexity_card_true_of_flip_sensitive
-- name    : CircuitComplexity.card_true_of_flip_sensitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:27.168279+00:00
-- url     : https://prove2.me/theorems/c695f1c0-c3dc-4226-b783-a7ed255f00e3
-- title:
--   Circuit Complexity: card true of flip sensitive
-- statement:
--   If `f` is flip-sensitive with `N ≥ 1`, its true-set has exactly `2^{N-1}` elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L290-L339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L290-L339

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit true
set_option autoImplicit true
open CircuitComplexity

theorem CircuitComplexity.card_true_of_flip_sensitive {N : Nat} (hN : 1 ≤ N)
    (f : BitString N → Bool)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x) :
    (Finset.univ.filter (fun x => f x = true)).card = 2 ^ (N - 1) := by sorry
