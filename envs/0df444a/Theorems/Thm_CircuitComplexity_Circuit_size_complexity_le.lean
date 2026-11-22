-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_size_complexity_le
-- name    : CircuitComplexity.Circuit.size_complexity_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:08:58.96494+00:00
-- url     : https://prove2.me/theorems/dd393d9d-c0b3-41fd-ba10-c02c40453a35
-- title:
--   Circuit: size complexity le
-- statement:
--   Any circuit computing `f` has size at least `sizeComplexity B f`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L248-L252
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L248-L252

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N : Nat} [NeZero N]

theorem CircuitComplexity.Circuit.size_complexity_le {G : Nat}
    (c : Circuit B N 1 G) (f : BitString N → Bool)
    (hf : (fun x => (c.eval x) 0) = f) :
    sizeComplexity B f ≤ c.size := by sorry
