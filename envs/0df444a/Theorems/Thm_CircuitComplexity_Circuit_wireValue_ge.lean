-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_wireValue_ge
-- name    : CircuitComplexity.Circuit.wireValue_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:08:57.21819+00:00
-- url     : https://prove2.me/theorems/3adaa893-9ea7-4661-8b95-752fcd1ab1de
-- title:
--   Circuit: wire Value ge
-- statement:
--   The Circuit construction uses the wire Value ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L139-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L139-L144

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

theorem CircuitComplexity.Circuit.wireValue_ge (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) (h : ¬ (w.val < N)) :
    c.wireValue input w =
      (c.gates ⟨w.val - N, by omega⟩).eval (c.wireValue input) := by sorry
