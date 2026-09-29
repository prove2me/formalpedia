-- Prove2me | solution 1 for exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/0db79935-4600-57a2-bebf-2e783d720d47

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful

set_option maxHeartbeats 1600000
set_option autoImplicit false

open Submodule in
theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ)
    {A : Type} [CommRing A] [Algebra R A]
    {M : Type} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite R M] [NoZeroSMulDivisors R M]
    (hfaith : ∀ t : A, (∀ x : M, t • x = 0) → t = 0) :
    ∃ b : ℕ, ∀ (m : ℕ) (t : A), (∀ x : M, ∃ y : M, t • x = ϖ ^ (m + b) • y) →
      ∃ t' : A, t = ϖ ^ m • t' := by
  classical
  haveI : Module.Free R M := Module.free_of_finite_type_torsion_free'

  let φ : A →ₗ[R] Module.End R M :=
    { toFun := fun t => DistribMulAction.toLinearMap R M t
      map_add' := fun t t' => LinearMap.ext fun x => by
        change (t + t') • x = t • x + t' • x
        exact add_smul t t' x
      map_smul' := fun r t => LinearMap.ext fun x => by
        change (r • t) • x = r • (t • x)
        exact smul_assoc r t x }
  have hφ : ∀ (t : A) (x : M), φ t x = t • x := fun t x => rfl
  have hφinj : ∀ t t' : A, φ t = φ t' → t = t' := by
    intro t t' h
    have h0 : t - t' = 0 := hfaith (t - t') (fun x => by
      have hx := LinearMap.congr_fun h x
      rw [hφ, hφ] at hx
      rw [sub_smul, hx, sub_self])
    exact sub_eq_zero.mp h0

  haveI : IsNoetherian R (Module.End R M) := isNoetherian_of_isNoetherianRing_of_finite R _
  let E := Module.End R M
  let Q := E ⧸ LinearMap.range φ
  haveI : IsNoetherian R Q := inferInstance

  let N : Submodule R Q := torsion' R Q (Submonoid.powers ϖ)
  have hN : ∀ q : Q, q ∈ N ↔ ∃ k : ℕ, ϖ ^ k • q = 0 := by
    intro q
    rw [mem_torsion'_iff]
    constructor
    · rintro ⟨⟨a, k, rfl⟩, ha⟩
      exact ⟨k, ha⟩
    · rintro ⟨k, hk⟩
      exact ⟨⟨ϖ ^ k, k, rfl⟩, hk⟩
  obtain ⟨s, hs⟩ : N.FG := IsNoetherian.noetherian N
  have hgen : ∀ q ∈ s, ∃ k : ℕ, ϖ ^ k • (q : Q) = 0 := by
    intro q hq
    have : q ∈ N := hs ▸ subset_span hq
    exact (hN q).1 this
  choose! kq hkq using hgen
  let b : ℕ := s.sup kq
  have hb' : ∀ q ∈ span R (s : Set Q), ϖ ^ b • q = 0 := by
    intro q hqN
    induction hqN using span_induction with
    | mem q hq =>
        have hle : kq q ≤ b := Finset.le_sup hq
        obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
        rw [hc, add_comm, pow_add, mul_smul, hkq q hq, smul_zero]
    | zero => exact smul_zero _
    | add q q' _ _ h h' => rw [smul_add, h, h', add_zero]
    | smul r q _ h => rw [smul_comm, h, smul_zero]
  have hb : ∀ q : Q, (∃ k : ℕ, ϖ ^ k • q = 0) → ϖ ^ b • q = 0 := by
    intro q hq
    exact hb' q (by rw [hs]; exact (hN q).2 hq)
  refine ⟨b, fun m t ht => ?_⟩

  choose y hy using ht
  have hinj : Function.Injective (fun z : M => ϖ ^ (m + b) • z) :=
    smul_right_injective M (pow_ne_zero _ hϖ.ne_zero)
  have hy_add : ∀ x x' : M, y (x + x') = y x + y x' := by
    intro x x'
    apply hinj
    simp only [smul_add, ← hy, smul_add]
  have hy_smul : ∀ (r : R) (x : M), y (r • x) = r • y x := by
    intro r x
    apply hinj
    simp only
    rw [← hy, smul_comm t r x, hy x, smul_comm]
  let u : E := { toFun := y, map_add' := hy_add, map_smul' := hy_smul }
  have hu : ϖ ^ (m + b) • u = φ t := by
    ext x
    rw [LinearMap.smul_apply, hφ]
    exact (hy x).symm

  have hcls : ϖ ^ b • u ∈ LinearMap.range φ := by
    have h1 : ϖ ^ (m + b) • (LinearMap.range φ).mkQ u = 0 := by
      rw [← map_smul, hu]
      exact (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self φ t)
    have h2 := hb _ ⟨m + b, h1⟩
    rw [← map_smul] at h2
    exact (Submodule.Quotient.mk_eq_zero _).1 h2
  obtain ⟨t₁, ht₁⟩ := hcls
  refine ⟨t₁, hφinj _ _ ?_⟩
  rw [← hu, map_smul, ht₁, pow_add, mul_smul]

end S_exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful
end P2MW
export P2MW.S_exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful (solution)
