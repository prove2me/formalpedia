-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_wireValue_lt
-- name    : CircuitComplexity.Circuit.wireValue_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:08:57.115284+00:00
-- url     : https://prove2.me/theorems/9caa5342-e40e-43a9-977b-1c40c5617a47
-- title:
--   Circuit: wire Value lt
-- statement:
--   The Circuit construction uses the wire Value lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L133-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L133-L137

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

theorem CircuitComplexity.Circuit.wireValue_lt (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) (h : w.val < N) :
    c.wireValue input w = input ⟨w.val, h⟩ := by sorry
