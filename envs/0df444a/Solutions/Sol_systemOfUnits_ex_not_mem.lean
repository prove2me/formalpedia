-- Prove2me | solution 1 for systemOfUnits.ex_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:00.517487+00:00
-- url     : https://prove2.me/submissions/65dd46a1-cbc5-40af-b4bc-fd62b018e317

module
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Theorems.Thm_systemOfUnits_finrank_spanA

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
include hp
include hf
set_option backward.isDefEq.respectTransparency false
namespace systemOfUnits
theorem _root_.solution [Module.Free ℤ G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < s) :
    ∃ g, ∀ (k : ℤ), k ≠ 0 → ¬(k • g ∈ Submodule.span A (Set.range S.units)) := by
  have := Fact.mk hp
  have : Module.Finite ℤ G := Module.finite_of_finrank_pos
    (by simp [hf, R.zero_le.trans_lt hR, hp.one_lt])
  refine Submodule.exists_of_finrank_lt
    ((Submodule.span A (Set.range S.units)).restrictScalars ℤ) ?_
  change finrank ℤ (Submodule.span A _) < _
  rw [finrank_spanA p hp G S.units S.linearIndependent, hf, mul_comm]
  exact Nat.mul_lt_mul_of_lt_of_le hR rfl.le hp.pred_pos
end systemOfUnits
