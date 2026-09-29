-- Prove2me | solution 1 for exists_forall_pow_smul_eq_smul_of_forall_exists_smul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/39025025-8b7a-5ac3-97eb-d69d6cfbf6de

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_forall_pow_smul_eq_smul_of_forall_exists_smul_eq_smul

set_option maxHeartbeats 1600000
set_option autoImplicit false

open Submodule in
theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ)
    {A : Type} [CommRing A] [Algebra R A]
    {M : Type} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite R M]
    (g : M) (hcyc : ∀ x : M, ∃ d : R, d ≠ 0 ∧ ∃ t : A, d • x = t • g) :
    ∃ a : ℕ, ∀ x : M, ∃ t : A, ϖ ^ a • x = t • g := by
  classical

  have hpt : ∀ x : M, ∃ (k : ℕ) (t : A), ϖ ^ k • x = t • g := by
    intro x
    obtain ⟨d, hd, t, ht⟩ := hcyc x
    obtain ⟨k, u, hdu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
    refine ⟨k, ((u⁻¹ : Rˣ) : R) • t, ?_⟩
    calc ϖ ^ k • x = (((u⁻¹ : Rˣ) : R) * (((u : Rˣ) : R) * ϖ ^ k)) • x := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ((u⁻¹ : Rˣ) : R) • (d • x) := by rw [mul_smul, hdu]
      _ = ((u⁻¹ : Rˣ) : R) • (t • g) := by rw [ht]
      _ = (((u⁻¹ : Rˣ) : R) • t) • g := by rw [smul_assoc]
  choose k t hkt using hpt
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine ⟨s.sup k, fun x => ?_⟩
  have hx : x ∈ span R (s : Set M) := by rw [hs]; exact mem_top
  induction hx using span_induction with
  | mem x hx =>
      obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := k) hx)
      refine ⟨ϖ ^ c • t x, ?_⟩
      rw [hc, add_comm, pow_add, mul_smul, hkt x, smul_assoc]
  | zero => exact ⟨0, by rw [smul_zero, zero_smul]⟩
  | add x x' _ _ h h' =>
      obtain ⟨t₁, h₁⟩ := h
      obtain ⟨t₂, h₂⟩ := h'
      exact ⟨t₁ + t₂, by rw [smul_add, h₁, h₂, add_smul]⟩
  | smul r x _ h =>
      obtain ⟨t₁, h₁⟩ := h
      exact ⟨r • t₁, by rw [smul_comm, h₁, smul_assoc]⟩

end S_exists_forall_pow_smul_eq_smul_of_forall_exists_smul_eq_smul
end P2MW
export P2MW.S_exists_forall_pow_smul_eq_smul_of_forall_exists_smul_eq_smul (solution)
