-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_wireValue_eq_of_unreferenced
-- name    : CircuitComplexity.Circuit.wireValue_eq_of_unreferenced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:26.549808+00:00
-- url     : https://prove2.me/theorems/f89e8bab-38e1-4126-86e0-4f45cf2451f9
-- title:
--   Circuit: wire Value eq of unreferenced
-- statement:
--   If no internal gate reads primary input `i`, wire values at wires
--       other than `i` are unchanged when input `i` is modified.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L36-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L36-L55

module
public import Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

theorem CircuitComplexity.Circuit.wireValue_eq_of_unreferenced
    (c : Circuit B N M G) (i : Fin N) (b : Bool)
    (hno : ∀ g : Fin G, ∀ k : Fin (c.gates g).fanIn,
      ((c.gates g).inputs k).val ≠ i.val)
    (x : BitString N) (w : Fin (N + G)) (hw : w.val ≠ i.val) :
    c.wireValue x w = c.wireValue (Function.update x i b) w := by sorry
