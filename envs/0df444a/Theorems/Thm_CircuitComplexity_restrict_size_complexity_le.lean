-- Prove2me | Theorems.Thm_CircuitComplexity_restrict_size_complexity_le
-- name    : CircuitComplexity.restrict_size_complexity_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:09.465816+00:00
-- url     : https://prove2.me/theorems/fd49338e-7012-45ae-8b6a-1e7673042129
-- title:
--   Circuit Complexity: restrict size complexity le
-- statement:
--   Hardwiring one input does not increase fan-in-2 AND/OR circuit complexity.
--
--       Given a circuit of size `s` computing `f`, we modify each gate in-place
--       (via `restrictGateP`): any input that referenced the hardwired variable
--       is redirected using the gate's negation flags to produce the correct
--       constant, without adding extra gates.  See `Circ.Internal.Nondeterminism`
--       for the construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism.lean#L82-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism.lean#L82-L91

module
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Nondeterminism
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
public import Definitions.Def_LeanPool_CircuitComplexity_Shannon
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}

theorem CircuitComplexity.restrict_size_complexity_le [CompleteBasis Basis.andOr2] [NeZero m]
    (f : BitString ((k + 1) + m) → Bool) (b : Bool) :
    Circuit.sizeComplexity Basis.andOr2 (restrictFirst f b) ≤
      Circuit.sizeComplexity Basis.andOr2 f := by sorry
