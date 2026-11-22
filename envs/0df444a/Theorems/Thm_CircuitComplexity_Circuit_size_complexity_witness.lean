-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_size_complexity_witness
-- name    : CircuitComplexity.Circuit.size_complexity_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:08:58.370964+00:00
-- url     : https://prove2.me/theorems/8148ebd1-b86d-44dc-8e22-73b7785f9170
-- title:
--   Circuit: size complexity witness
-- statement:
--   For a complete basis, `sizeComplexity` is realized by some circuit.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L255-L259
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L255-L259

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N : Nat} [NeZero N]

theorem CircuitComplexity.Circuit.size_complexity_witness [CompleteBasis B]
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit B N 1 G,
      c.size = sizeComplexity B f ∧ (fun x => (c.eval x) 0) = f := by sorry
