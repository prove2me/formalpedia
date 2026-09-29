-- Prove2me | solution 1 for groupCohomology.exists_inflate_H1_injective_range_iff_split
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/2f3752f5-f9f0-5873-8585-37bd8e8be3e5

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_inflate_H1_injective_range_iff_split

set_option autoImplicit false
open CategoryTheory groupCohomology

namespace InfRes1

universe v w

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

lemma isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.instIsAlgClosure ℚ <;> first | rfl | exact Subsingleton.elim _ _
local instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) :=
  haveI := isAlgClosureQbar
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]

noncomputable abbrev pi : Γ →* (↥F ≃ₐ[ℚ] ↥F) := AlgEquiv.restrictNormalHom ↥F

lemma pi_surjective : Function.Surjective (pi F) :=
  AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ)

omit [NumberField ↥F] in
lemma pi_eq_one_iff (s : Γ) : pi F s = 1 ↔ s ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, AlgEquiv.ext_iff]
  constructor
  · intro h y hy
    have h1 := congrArg (algebraMap ↥F (AlgebraicClosure ℚ)) (h ⟨y, hy⟩)
    rw [AlgEquiv.one_apply] at h1
    change algebraMap ↥F (AlgebraicClosure ℚ) (s.restrictNormal ↥F ⟨y, hy⟩) = y at h1
    rwa [AlgEquiv.restrictNormal_commutes] at h1
  · intro h x
    apply (algebraMap ↥F (AlgebraicClosure ℚ)).injective
    change algebraMap ↥F (AlgebraicClosure ℚ) (s.restrictNormal ↥F x) = algebraMap ↥F (AlgebraicClosure ℚ) x
    rw [AlgEquiv.restrictNormal_commutes]
    exact h x x.2

lemma pi_eq_pi_iff (γ γ' : Γ) : pi F γ = pi F γ' ↔ γ⁻¹ * γ' ∈ F.fixingSubgroup := by
  rw [← pi_eq_one_iff, map_mul, map_inv, inv_mul_eq_one, eq_comm]

noncomputable abbrev sec : (↥F ≃ₐ[ℚ] ↥F) → Γ := Function.surjInv (pi_surjective F)

lemma pi_sec (σ : ↥F ≃ₐ[ℚ] ↥F) : pi F (sec F σ) = σ := Function.surjInv_eq (pi_surjective F) σ

lemma apply_eq_of_pi_eq {X : Type v} (ny : Γ → X) (hn : ∀ (γ s : Γ), s ∈ F.fixingSubgroup → ny (γ * s) = ny γ)
    {γ γ' : Γ} (h : pi F γ = pi F γ') : ny γ = ny γ' := by
  have hs := (pi_eq_pi_iff F γ γ').1 h
  have := hn γ (γ⁻¹ * γ') hs
  rw [mul_inv_cancel_left] at this
  exact this.symm

variable {k : Type} [CommRing k] (M : Rep k Γ) (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) (β : B →+ M) (hβ : Function.Bijective β)
  (hβeq : ∀ (γ : Γ) (b : B), β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = M.ρ γ (β b))

include hβ hβeq in

theorem inj (n : cocycles₁ B) (ny : cocycles₁ M)
    (hny : ∀ γ : Γ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ)))
    (h0 : (H1π M).hom ny = 0) : (H1π B).hom n = 0 := by
  have h0' : H1π M ny = 0 := h0
  rw [H1π_eq_zero_iff] at h0'
  show H1π B n = 0
  rw [H1π_eq_zero_iff]
  obtain ⟨m, hm⟩ := h0'
  obtain ⟨b, rfl⟩ := hβ.2 m
  refine ⟨b, funext fun σ => ?_⟩
  obtain ⟨γ, rfl⟩ := pi_surjective F σ
  have hγ := congrFun hm γ
  rw [d₀₁_hom_apply] at hγ ⊢
  apply hβ.1
  change β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b - b) = β (n (AlgEquiv.restrictNormalHom ↥F γ))
  rw [map_sub, hβeq, ← hny γ, ← hγ]

include hβ hβeq in

theorem im (ny : cocycles₁ M)
    (hn : ∀ (γ s : Γ), s ∈ F.fixingSubgroup → ny (γ * s) = ny γ) :
    ∃ n : cocycles₁ B, ∀ γ : Γ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ)) := by
  let e : B ≃+ M := AddEquiv.ofBijective β hβ
  have eβ : ∀ m, β (e.symm m) = m := e.apply_symm_apply
  have key : ∀ γ : Γ, ny (sec F (pi F γ)) = ny γ := fun γ =>
    apply_eq_of_pi_eq F ny hn ((pi_sec F (pi F γ)))
  refine ⟨⟨fun σ => e.symm (ny (sec F σ)), (mem_cocycles₁_iff _).2 fun σ τ => ?_⟩, fun γ => ?_⟩
  · obtain ⟨γ, rfl⟩ := pi_surjective F σ
    obtain ⟨δ, rfl⟩ := pi_surjective F τ
    apply hβ.1
    rw [map_add, hβeq, eβ, eβ, eβ, ← map_mul, key, key, key]
    exact (mem_cocycles₁_iff ny).1 ny.2 γ δ
  · change ny γ = β (e.symm (ny (sec F (pi F γ))))
    rw [eβ, key]

include hβ hβeq in

theorem inflate_mem (n : cocycles₁ B) :
    (fun γ : Γ => β (n (AlgEquiv.restrictNormalHom ↥F γ))) ∈ cocycles₁ M := by
  refine (mem_cocycles₁_iff _).2 fun γ δ => ?_
  change β (n (AlgEquiv.restrictNormalHom ↥F (γ * δ))) = M.ρ γ (β (n (AlgEquiv.restrictNormalHom ↥F δ))) + β (n (AlgEquiv.restrictNormalHom ↥F γ))
  rw [map_mul, (mem_cocycles₁_iff n).1 n.2, map_add, hβeq]

noncomputable def inflate : cocycles₁ B →+ cocycles₁ M where
  toFun n := ⟨fun γ => β (n (AlgEquiv.restrictNormalHom ↥F γ)), inflate_mem F M B β hβ hβeq n⟩
  map_zero' := by apply Subtype.ext; funext γ; show β 0 = 0; exact map_zero β
  map_add' n n' := by
    apply Subtype.ext; funext γ
    show β (n (AlgEquiv.restrictNormalHom ↥F γ) + n' (AlgEquiv.restrictNormalHom ↥F γ)) = β (n _) + β (n' _)
    exact map_add β _ _

lemma inflate_apply (n : cocycles₁ B) (γ : Γ) : inflate F M B β hβ hβeq n γ = β (n (AlgEquiv.restrictNormalHom ↥F γ)) := rfl

include hβ hβeq in

lemma H1π_inflate_eq (n n' : cocycles₁ B) (h : H1π B n = H1π B n') :
    H1π M (inflate F M B β hβ hβeq n) = H1π M (inflate F M B β hβ hβeq n') := by
  rw [H1π_eq_iff] at h ⊢
  obtain ⟨b, hb⟩ := h
  refine ⟨β b, funext fun γ => ?_⟩
  have hγ := congrFun hb (AlgEquiv.restrictNormalHom ↥F γ)
  rw [d₀₁_hom_apply] at hγ ⊢
  change M.ρ γ (β b) - β b = β (n _) - β (n' _)
  rw [← hβeq, ← map_sub, ← map_sub]
  congr 1

noncomputable abbrev secH : H1 B → cocycles₁ B :=
  Function.surjInv ((ModuleCat.epi_iff_surjective (H1π B)).1 inferInstance)

lemma H1π_secH (x : H1 B) : H1π B (secH F B x) = x :=
  Function.surjInv_eq ((ModuleCat.epi_iff_surjective (H1π B)).1 inferInstance) x

noncomputable def infl : groupCohomology B 1 →+ H1 M where
  toFun x := H1π M (inflate F M B β hβ hβeq (secH F B x))
  map_zero' := by
    have h : H1π B (secH F B 0) = H1π B 0 := by rw [H1π_secH, map_zero]
    rw [H1π_inflate_eq F M B β hβ hβeq _ _ h, map_zero, map_zero]
  map_add' x y := by
    have h : H1π B (secH F B (x + y)) = H1π B (secH F B x + secH F B y) := by rw [map_add, H1π_secH, H1π_secH, H1π_secH]
    rw [H1π_inflate_eq F M B β hβ hβeq _ _ h, map_add, map_add]

lemma infl_H1π (n : cocycles₁ B) : infl F M B β hβ hβeq (H1π B n) = H1π M (inflate F M B β hβ hβeq n) :=
  H1π_inflate_eq F M B β hβ hβeq _ _ (H1π_secH F B _)

include hβ hβeq in
theorem pkg [Fintype B] :
    ∃ infl : groupCohomology B 1 →+ H1 M,
      (∀ (n : cocycles₁ B) (ny : cocycles₁ M),
        (∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ))) →
          infl ((H1π B).hom n) = (H1π M).hom ny) ∧
      Function.Injective infl ∧
      (∀ y : H1 M, (∃ x, infl x = y) ↔
        ∃ ny : cocycles₁ M, (H1π M).hom ny = y ∧
          (∀ (γ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → ny (γ * s) = ny γ) ∧
          (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F.fixingSubgroup → ny s = 0)) := by
  have pin : ∀ (n : cocycles₁ B) (ny : cocycles₁ M),
      (∀ γ : Γ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ))) → infl F M B β hβ hβeq ((H1π B).hom n) = (H1π M).hom ny := by
    intro n ny hny
    have e : ny = inflate F M B β hβ hβeq n := Subtype.ext (funext hny)
    rw [e]
    exact infl_H1π F M B β hβ hβeq n
  refine ⟨infl F M B β hβ hβeq, pin, ?_, fun y => ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using H1_induction_on with | @h n =>
    have h0 : (H1π M).hom (inflate F M B β hβ hβeq n) = 0 := by
      rw [← pin n _ (fun γ => rfl)]; exact hx
    exact inj F M B β hβ hβeq n _ (fun γ => rfl) h0
  · rintro ⟨x, rfl⟩
    induction x using H1_induction_on with | @h n =>
    refine ⟨inflate F M B β hβ hβeq n, (pin n _ (fun γ => rfl)).symm, fun γ s hs => ?_, fun s hs => ?_⟩
    · rw [inflate_apply, inflate_apply, map_mul, (pi_eq_one_iff F s).2 hs, mul_one]
    · rw [inflate_apply, (pi_eq_one_iff F s).2 hs, cocycles₁_map_one, map_zero]
  · rintro ⟨ny, rfl, hn, -⟩
    obtain ⟨n, hn'⟩ := im F M B β hβ hβeq ny hn
    exact ⟨(H1π B).hom n, pin n ny hn'⟩

end InfRes1

theorem solution
    {k : Type} [CommRing k] (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M) (hβ : Function.Bijective β)
    (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
      β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = M.ρ γ (β b)) :
    ∃ infl : groupCohomology B 1 →+ H1 M,
      (∀ (n : cocycles₁ B) (ny : cocycles₁ M),
        (∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ))) →
          infl ((H1π B).hom n) = (H1π M).hom ny) ∧
      Function.Injective infl ∧
      (∀ y : H1 M, (∃ x, infl x = y) ↔
        ∃ ny : cocycles₁ M, (H1π M).hom ny = y ∧
          (∀ (γ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → ny (γ * s) = ny γ) ∧
          (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F.fixingSubgroup → ny s = 0)) :=
  InfRes1.pkg F M B β hβ hβeq

end S_groupCohomology_exists_inflate_H1_injective_range_iff_split
end P2MW
export P2MW.S_groupCohomology_exists_inflate_H1_injective_range_iff_split (solution)
