-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_size_complexity_pos
-- name    : CircuitComplexity.Circuit.size_complexity_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:10.287426+00:00
-- url     : https://prove2.me/theorems/72279ec4-1c3c-4f2e-a1ca-5b71a613fd09
-- title:
--   Circuit: size complexity pos
-- statement:
--   For a complete basis, circuit size complexity is always positive.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L239-L245
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L239-L245

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N : Nat} [NeZero N]

theorem CircuitComplexity.Circuit.size_complexity_pos [CompleteBasis B]
    (f : BitString N → Bool) :
    0 < sizeComplexity B f := by sorry
