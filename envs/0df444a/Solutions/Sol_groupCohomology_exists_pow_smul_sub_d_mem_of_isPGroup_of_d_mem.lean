-- Prove2me | solution 1 for groupCohomology.exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a6b94402-6a3a-5fd2-98a8-d2876435e990

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem solution
    {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (A : Rep.{0} ℤ G) (W : AddSubgroup A) (hW : ∀ (g : G) (a : A), a ∈ W → A.ρ g a ∈ W) [W.FiniteIndex]
    (ν : (Fin 1 → G) → A)
    (hν : ∀ g : Fin 2 → G, ((inhomogeneousCochains A).d 1 2).hom ν g ∈ W) :
    ∃ (m : (Fin 0 → G) → A) (k : ℕ),
      ∀ g : Fin 1 → G, (p ^ k : ℤ) • (ν g - ((inhomogeneousCochains A).d 0 1).hom m g) ∈ W := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hp : p.Prime := Fact.out

  let c : G → (Fin 1 → G) := fun g _ => g
  have hc : ∀ t : Fin 1 → G, t = c (t 0) := fun t => funext fun i => by
    rw [Subsingleton.elim i 0]
  have hν₁ : ∀ g : G, (cochainsIso₁ A).hom ν g = ν (c g) := fun g => rfl

  have hcoc : ∀ g h : G, A.ρ g (ν (c h)) - ν (c (g * h)) + ν (c g) ∈ W := by
    intro g h
    have e := congrArg ModuleCat.Hom.hom (groupCohomology.comp_d₁₂_eq A)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at e
    have e' := congrFun (DFunLike.congr_fun e ν) (g, h)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, d₁₂_hom_apply, hν₁, hν₁, hν₁] at e'
    rw [e']
    exact hν _

  let s : A := ∑ h : G, ν (c h)
  have hsum : ∀ g : G, (Fintype.card G : ℤ) • ν (c g) + (A.ρ g s - s) ∈ W := by
    intro g
    have h1 : ∑ h : G, (A.ρ g (ν (c h)) - ν (c (g * h)) + ν (c g)) ∈ W :=
      W.sum_mem fun h _ => hcoc g h
    have h2 : ∑ h : G, ν (c (g * h)) = s := Equiv.sum_comp (Equiv.mulLeft g) (fun h => ν (c h))
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← map_sum, h2, Finset.sum_const, Finset.card_univ,
      ← natCast_zsmul] at h1
    convert h1 using 1
    abel

  have hd0 : ∀ (x : A) (t : Fin 1 → G),
      ((inhomogeneousCochains A).d 0 1).hom ((cochainsIso₀ A).inv x) t = A.ρ (t 0) x - x := by
    intro x t
    rw [groupCohomology.eq_d₀₁_comp_inv_apply A x]
    show (d₀₁ A).hom x (t 0) = _
    rw [d₀₁_hom_apply]

  obtain ⟨a, ha⟩ := hG.exists_card_eq
  rw [Nat.card_eq_fintype_card] at ha
  have hidx0 : W.index ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  obtain ⟨k, n', hn', hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hidx0 p hp.one_lt.ne'
  have hcop : IsCoprime ((p ^ a : ℕ) : ℤ) (n' : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hn'))
  obtain ⟨u, v, huv⟩ := hcop
  have hidx : ∀ x : A, (W.index : ℤ) • x ∈ W := fun x => by
    rw [natCast_zsmul]; exact W.nsmul_index_mem x

  refine ⟨(cochainsIso₀ A).inv (-(u • s)), k, fun t => ?_⟩
  rw [hd0, hc t]
  set g := t 0
  have hx : A.ρ g (-(u • s)) - -(u • s) = -(u • (A.ρ g s - s)) := by
    rw [map_neg, map_zsmul, smul_sub]; abel
  have key : (p ^ k : ℤ) • ν (c g) =
      (u * p ^ k) • ((Fintype.card G : ℤ) • ν (c g)) + v • ((W.index : ℤ) • ν (c g)) := by
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    rw [ha, hn]
    push_cast at huv ⊢
    linear_combination (-(p : ℤ) ^ k) * huv
  have hfin : (p ^ k : ℤ) • (ν (c g) - (A.ρ g (-(u • s)) - -(u • s))) =
      (u * p ^ k) • ((Fintype.card G : ℤ) • ν (c g) + (A.ρ g s - s)) + v • ((W.index : ℤ) • ν (c g)) := by
    rw [hx, smul_sub, key]
    module
  show (p ^ k : ℤ) • (ν (c g) - (A.ρ (c g 0) (-(u • s)) - -(u • s))) ∈ W
  rw [show c g 0 = g from rfl, hfin]
  exact W.add_mem (W.zsmul_mem (hsum g) _) (W.zsmul_mem (hidx _) _)

end S_groupCohomology_exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem
end P2MW
export P2MW.S_groupCohomology_exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem (solution)
