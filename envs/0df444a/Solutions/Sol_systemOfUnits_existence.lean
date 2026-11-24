-- Prove2me | solution 1 for systemOfUnits.existence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:50.187521+00:00
-- url     : https://prove2.me/submissions/c302ecf0-a5c1-4596-b321-2556289cf709

module
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Theorems.Thm_P2M_systemOfUnits_existence___b11e56e036a6

set_option autoImplicit false
@[expose] public section
public section
open FiniteDimensional
open NumberField
variable (p : ℕ) (hp : Nat.Prime p)
open Module Finset
variable (G : Type*) [AddCommGroup G] (s : ℕ) (hf : finrank ℤ G = s * (p - 1))
local notation "A" => (CyclotomicIntegers p)
open systemOfUnits
include hp hf
variable [Module.Free ℤ G]
namespace systemOfUnits
theorem _root_.solution [Module A G] : Nonempty (systemOfUnits p G s) := existence'' p hp G s hf rfl.le
end systemOfUnits
