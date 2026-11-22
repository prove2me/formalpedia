-- Prove2me | Theorems.Thm_CircuitComplexity_Schnorr_restriction_eliminates_two
-- name    : CircuitComplexity.Schnorr.restriction_eliminates_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:13.544818+00:00
-- url     : https://prove2.me/theorems/48a1b2f2-930c-4acd-9f79-903058320b1b
-- title:
--   Schnorr: restriction eliminates two
-- statement:
--   Key inductive step: restricting one variable of a totally essential XOR circuit
--       yields a circuit for XOR on one fewer input, with at least 2 fewer gates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L1365-L1411
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L1365-L1411

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

theorem CircuitComplexity.Schnorr.restriction_eliminates_two {n s : Nat} (d : CircDesc (n + 1) s)
    (hs : 0 < s) (hn : 0 < n) (comp : Bool)
    (heval : ∀ x, evalD hs d x = comp.xor (xorBool (n + 1) x))
    (hessential : ∀ (a : Fin (n + 1)) (x : BitString (n + 1)),
      evalD hs d x ≠ evalD hs d (Function.update x a (!x a))) :
    ∃ (s' : Nat) (d' : CircDesc n s') (hs' : 0 < s') (comp' : Bool),
      s' + 2 ≤ s ∧ (∀ x, evalD hs' d' x = comp'.xor (xorBool n x)) := by sorry
