-- Prove2me | solution 1 for groupCohomology.exists_two_cocycle_coind_apply_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/7d3a1860-f5ed-5a03-bbe4-3fcefb8806b2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_two_cocycle_coind_apply_one_eq

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem solution
    {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (A : Rep k S)
    (c : (Fin 2 → S) → A) (hc : inhomogeneousCochains.d A 2 c = 0) :
    ∃ (F : (Fin 2 → G) → Rep.coind S.subtype A)
      (_ : inhomogeneousCochains.d (Rep.coind S.subtype A) 2 F = 0),
      ∀ s : Fin 2 → S, (F (fun i => (s i : G))).1 1 = c s := by
  classical

  let R : Setoid G := QuotientGroup.rightRel S
  let o : G → G := fun x => (Quotient.mk R x).out
  have ho : ∀ x : G, o x * x⁻¹ ∈ S := by
    intro x
    have h := Quotient.mk_out (s := R) x
    rw [QuotientGroup.rightRel_apply] at h
    simpa using S.inv_mem h
  have ho_mul : ∀ (s : S) (x : G), o ((s : G) * x) = o x := by
    intro s x
    show (Quotient.mk R ((s : G) * x)).out = (Quotient.mk R x).out
    congr 1
    apply Quotient.sound
    show QuotientGroup.rightRel S ((s : G) * x) x
    rw [QuotientGroup.rightRel_apply]
    simpa [mul_assoc] using S.inv_mem s.2
  let τ : G := o 1
  have hτ : τ ∈ S := by simpa using ho 1
  let t : G → G := fun x => τ⁻¹ * o x
  have ht_mul : ∀ (s : S) (x : G), t ((s : G) * x) = t x := by
    intro s x; show τ⁻¹ * o ((s : G) * x) = τ⁻¹ * o x; rw [ho_mul]
  have ht_one : t 1 = 1 := by show τ⁻¹ * o 1 = 1; exact inv_mul_cancel τ
  have hst : ∀ x : G, x * (t x)⁻¹ ∈ S := by
    intro x
    show x * (τ⁻¹ * o x)⁻¹ ∈ S
    rw [mul_inv_rev, inv_inv, ← mul_assoc]
    exact S.mul_mem (by simpa using S.inv_mem (ho x)) hτ

  let sf : G → S := fun x => ⟨x * (t x)⁻¹, hst x⟩
  have hd_mem : ∀ x g : G, t x * g * (t (x * g))⁻¹ ∈ S := by
    intro x g
    have h1 : t x * g * (t (x * g))⁻¹ = (x * (t x)⁻¹)⁻¹ * (x * g * (t (x * g))⁻¹) := by group
    rw [h1]
    exact S.mul_mem (S.inv_mem (hst x)) (hst (x * g))
  let d : G → G → S := fun x g => ⟨t x * g * (t (x * g))⁻¹, hd_mem x g⟩

  have hsf_mul : ∀ x g : G, sf (x * g) = sf x * d x g := by
    intro x g; apply Subtype.ext
    show x * g * (t (x * g))⁻¹ = x * (t x)⁻¹ * (t x * g * (t (x * g))⁻¹)
    group
  have hd_mul : ∀ x g₁ g₂ : G, d x (g₁ * g₂) = d x g₁ * d (x * g₁) g₂ := by
    intro x g₁ g₂; apply Subtype.ext
    show t x * (g₁ * g₂) * (t (x * (g₁ * g₂)))⁻¹ = t x * g₁ * (t (x * g₁))⁻¹ * (t (x * g₁) * g₂ * (t (x * g₁ * g₂))⁻¹)
    rw [← mul_assoc x g₁ g₂]; group
  have hd_smul : ∀ (s : S) (x g : G), d ((s : G) * x) g = d x g := by
    intro s x g; apply Subtype.ext
    show t ((s : G) * x) * g * (t ((s : G) * x * g))⁻¹ = t x * g * (t (x * g))⁻¹
    rw [mul_assoc (s : G) x g, ht_mul, ht_mul]
  have hsf_smul : ∀ (s : S) (x : G), sf ((s : G) * x) = s * sf x := by
    intro s x; apply Subtype.ext
    show (s : G) * x * (t ((s : G) * x))⁻¹ = (s : G) * (x * (t x)⁻¹)
    rw [ht_mul, mul_assoc]
  have ht_S : ∀ s : S, t (s : G) = 1 := by
    intro s; have := ht_mul s 1; rw [mul_one] at this; rw [this, ht_one]
  have hsf_one : sf 1 = 1 := by apply Subtype.ext; show (1 : G) * (t 1)⁻¹ = 1; rw [ht_one]; simp
  have hd_one_S : ∀ s : S, d 1 (s : G) = s := by
    intro s; apply Subtype.ext; show t 1 * (s : G) * (t (1 * (s : G)))⁻¹ = s
    rw [one_mul, ht_one, ht_S, one_mul, inv_one, mul_one]
  have hd_S_S : ∀ s₁ s₂ : S, d (s₁ : G) (s₂ : G) = s₂ := by
    intro s₁ s₂; apply Subtype.ext; show t (s₁ : G) * (s₂ : G) * (t ((s₁ : G) * (s₂ : G)))⁻¹ = s₂
    rw [ht_S, ← Subgroup.coe_mul, ht_S]; simp

  let Fv : (Fin 2 → G) → G → A := fun g x => A.ρ (sf x) (c ![d x (g 0), d (x * g 0) (g 1)])
  have hFv : ∀ g : Fin 2 → G, Fv g ∈ Representation.coindV S.subtype A.ρ := by
    intro g
    rw [Representation.mem_coindV]
    intro s x
    show A.ρ (sf ((s : G) * x)) (c ![d ((s : G) * x) (g 0), d ((s : G) * x * g 0) (g 1)])
      = A.ρ s (A.ρ (sf x) (c ![d x (g 0), d (x * g 0) (g 1)]))
    rw [hsf_smul, map_mul, mul_assoc (s : G) x (g 0), hd_smul, hd_smul]
    rfl
  let F : (Fin 2 → G) → Rep.coind S.subtype A := fun g => ⟨Fv g, hFv g⟩
  have hF1 : ∀ (g : Fin 2 → G) (x : G), (F g).1 x = A.ρ (sf x) (c ![d x (g 0), d (x * g 0) (g 1)]) :=
    fun g x => rfl
  refine ⟨F, ?_, ?_⟩
  ·
    ext g : 1
    apply Subtype.ext
    funext x
    rw [inhomogeneousCochains.d_hom_apply]

    have hρ : ∀ (h : G) (f : Rep.coind S.subtype A) (y : G),
        (((Rep.coind S.subtype A).ρ h) f).1 y = f.1 (y * h) := fun _ _ _ => rfl
    have e0 : Fin.contractNth 0 (· * ·) g = ![g 0 * g 1, g 2] := by
      ext i; fin_cases i <;> simp [Fin.contractNth]
    have e1 : Fin.contractNth 1 (· * ·) g = ![g 0, g 1 * g 2] := by
      ext i; fin_cases i <;> simp [Fin.contractNth]
    have e2 : Fin.contractNth 2 (· * ·) g = ![g 0, g 1] := by
      ext i; fin_cases i <;> simp [Fin.contractNth]

    have hcd := congrFun hc ![d x (g 0), d (x * g 0) (g 1), d (x * g 0 * g 1) (g 2)]
    rw [inhomogeneousCochains.d_hom_apply] at hcd
    have f0 : Fin.contractNth 0 (· * ·) ![d x (g 0), d (x * g 0) (g 1), d (x * g 0 * g 1) (g 2)]
        = ![d x (g 0) * d (x * g 0) (g 1), d (x * g 0 * g 1) (g 2)] := by
      ext i; fin_cases i <;> simp [Fin.contractNth]
    have f1 : Fin.contractNth 1 (· * ·) ![d x (g 0), d (x * g 0) (g 1), d (x * g 0 * g 1) (g 2)]
        = ![d x (g 0), d (x * g 0) (g 1) * d (x * g 0 * g 1) (g 2)] := by
      ext i; fin_cases i <;> simp [Fin.contractNth]
    have f2 : Fin.contractNth 2 (· * ·) ![d x (g 0), d (x * g 0) (g 1), d (x * g 0 * g 1) (g 2)]
        = ![d x (g 0), d (x * g 0) (g 1)] := by
      ext i; fin_cases i <;> simp [Fin.contractNth]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, add_zero,
      f0, f1, f2, Fin.val_zero, Fin.val_one, Fin.val_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply] at hcd
    have htail : (fun i : Fin 2 => ![d x (g 0), d (x * g 0) (g 1), d (x * g 0 * g 1) (g 2)] i.succ)
        = ![d (x * g 0) (g 1), d (x * g 0 * g 1) (g 2)] := by
      funext i; fin_cases i <;> rfl
    rw [htail] at hcd

    rw [Submodule.coe_add, Pi.add_apply, hρ, Submodule.coe_sum, Finset.sum_apply]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, add_zero,
      Submodule.coe_smul, Pi.smul_apply, e0, e1, e2, Fin.val_zero, Fin.val_one,
      Fin.val_two, hF1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

    rw [hsf_mul x (g 0), map_mul, hd_mul x (g 0) (g 1), hd_mul (x * g 0) (g 1) (g 2), Module.End.mul_apply,
      show x * (g 0 * g 1) = x * g 0 * g 1 from (mul_assoc _ _ _).symm]
    show _ = (0 : A)
    rw [← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add, ← map_add]
    rw [show (0 : (Fin 3 → S) → A) ![d x (g 0), d (x * g 0) (g 1), d (x * g 0 * g 1) (g 2)] = (0 : A) from rfl] at hcd
    rw [hcd, map_zero]
  ·
    intro s
    have h := hF1 (fun i => (s i : G)) 1
    rw [h, hsf_one, map_one, one_mul, hd_one_S (s 0), hd_S_S (s 0) (s 1)]
    show c ![s 0, s 1] = c s
    congr 1
    funext i; fin_cases i <;> rfl

end S_groupCohomology_exists_two_cocycle_coind_apply_one_eq
end P2MW
export P2MW.S_groupCohomology_exists_two_cocycle_coind_apply_one_eq (solution)
