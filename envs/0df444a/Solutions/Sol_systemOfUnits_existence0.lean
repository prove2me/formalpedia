-- Prove2me | solution 1 for systemOfUnits.existence0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:07.961823+00:00
-- url     : https://prove2.me/submissions/8e097954-c33a-4c36-b1c1-99806f1c1c15

module
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits

set_option autoImplicit false
@[expose] public section
public section
open FiniteDimensional
open NumberField
variable (p : ℕ) (hp : Nat.Prime p)
open Module Finset
variable (G : Type*) [AddCommGroup G] (s : ℕ) (hf : finrank ℤ G = s * (p - 1))
local notation "A" => (CyclotomicIntegers p)
variable [Module (CyclotomicIntegers p) G]
open systemOfUnits
namespace systemOfUnits
theorem _root_.solution : Nonempty (systemOfUnits p G 0) :=
  ⟨⟨fun _ ↦ 0, linearIndependent_empty_type⟩⟩
end systemOfUnits
