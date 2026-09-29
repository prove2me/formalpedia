-- Prove2me | solution 1 for groupCohomology.H2inf_injective_of_subsingleton_H1_res
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/3be320ae-a565-5cd7-a7c2-969a225e06ab

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_H2inf_injective_of_subsingleton_H1_res

set_option autoImplicit false

universe u

p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_H2inf_injective_of_subsingleton_H1_res.groupCohomology Rep"

namespace groupCohomology
p2m_export "groupCohomology" "mem_cocycles₁_def cocycles₂_map_one_fst H1π cocycles₂ H1π_eq_zero_iff d₁₂_hom_apply coe_mapCocycles₂ H2π_comp_map_apply map cocycles₂_map_one_snd d₀₁_hom_apply H2_induction_on cocycles₁ H2π_eq_zero_iff H1"
p2m_open "groupCohomology"

section FiveTermDegreeTwo

variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {S : Subgroup G} [S.Normal]

section BoundaryWitness

variable (β : cocycles₂ (A.quotientToInvariants S)) (f : G → A)
  (hf : ∀ g h : G, A.ρ g (f h) - f (g * h) + f g = ↑(β ((g : G ⧸ S), (h : G ⧸ S))))

include hf

private theorem boundaryWitness_apply_one : f 1 = ↑(β (1, 1)) := by
  have := hf 1 1
  simpa using this

private theorem boundaryWitness_ρ_apply_one (s : G) (hs : s ∈ S) : A.ρ s (f 1) = f 1 := by
  rw [boundaryWitness_apply_one β f hf]
  exact (β (1, 1)).2 ⟨s, hs⟩

private theorem boundaryWitness_beta_one_snd (g : G) :
    (β ((g : G ⧸ S), 1) : A) = A.ρ g (f 1) := by
  rw [cocycles₂_map_one_snd β, boundaryWitness_apply_one β f hf]
  rfl

private theorem boundaryWitness_beta_one_fst (g : G) :
    (β (1, (g : G ⧸ S)) : A) = f 1 := by
  rw [cocycles₂_map_one_fst β, boundaryWitness_apply_one β f hf]

private theorem restrictedCocycle_cocycle_identity (s₁ s₂ : G) (hs₁ : s₁ ∈ S) (hs₂ : s₂ ∈ S) :
    A.ρ s₁ (f s₂ - f 1) - (f (s₁ * s₂) - f 1) + (f s₁ - f 1) = 0 := by
  have h12 := hf s₁ s₂
  rw [show ((s₁ : G ⧸ S) : G ⧸ S) = 1 from (QuotientGroup.eq_one_iff s₁).mpr hs₁,
    show ((s₂ : G ⧸ S) : G ⧸ S) = 1 from (QuotientGroup.eq_one_iff s₂).mpr hs₂,
    ← boundaryWitness_apply_one β f hf] at h12
  have hρ : A.ρ s₁ (f 1) = f 1 := boundaryWitness_ρ_apply_one β f hf s₁ hs₁
  rw [map_sub]
  linear_combination (norm := abel) h12 - hρ

private def restrictedCocycleOfInfBoundary : cocycles₁ (Rep.res S.subtype A) :=
  ⟨fun s => f (s : G) - f 1, by
    rw [mem_cocycles₁_def]
    intro s₁ s₂

    exact restrictedCocycle_cocycle_identity β f hf s₁ s₂ s₁.2 s₂.2⟩

private theorem restrictedCocycleOfInfBoundary_apply (s : S) :
    (restrictedCocycleOfInfBoundary β f hf : S → A) s = f (s : G) - f 1 := rfl

variable (a : A) (ha : ∀ s ∈ S, f s - f 1 = A.ρ s a - a)

include ha

set_option linter.unusedSectionVars false in

private theorem correctedCochain_apply_mem (s : G) (hs : s ∈ S) :
    f s - (A.ρ s a - a) = f 1 := by
  linear_combination (norm := abel) ha s hs

private theorem correctedCochain_right_invariant (g s : G) (hs : s ∈ S) :
    f (g * s) - (A.ρ (g * s) a - a) = f g - (A.ρ g a - a) := by

  have h := hf g s
  rw [show ((s : G ⧸ S) : G ⧸ S) = 1 from (QuotientGroup.eq_one_iff s).mpr hs,
    boundaryWitness_beta_one_snd β f hf] at h

  have hfs : A.ρ g (f s - (A.ρ s a - a)) = A.ρ g (f 1) :=
    congrArg (A.ρ g) (correctedCochain_apply_mem β f hf a ha s hs)
  rw [map_sub, map_sub, show (A.ρ g) ((A.ρ s) a) = A.ρ (g * s) a by rw [map_mul]; rfl] at hfs
  linear_combination (norm := abel) hfs - h

private theorem correctedCochain_mem_invariants (g : G) (s : G) (hs : s ∈ S) :
    A.ρ s (f g - (A.ρ g a - a)) = f g - (A.ρ g a - a) := by

  have h := hf s g
  rw [show ((s : G ⧸ S) : G ⧸ S) = 1 from (QuotientGroup.eq_one_iff s).mpr hs,
    boundaryWitness_beta_one_fst β f hf] at h
  have hfs : f s - (A.ρ s a - a) = f 1 := correctedCochain_apply_mem β f hf a ha s hs
  have hgs : f (s * g) - (A.ρ (s * g) a - a) = f g - (A.ρ g a - a) := by
    have := correctedCochain_right_invariant β f hf a ha g (g⁻¹ * s * g)
      (Subgroup.Normal.conj_mem' ‹_› s hs g)
    rwa [show g * (g⁻¹ * s * g) = s * g by group] at this
  rw [map_sub, map_sub, show (A.ρ s) ((A.ρ g) a) = A.ρ (s * g) a by rw [map_mul]; rfl]
  linear_combination (norm := abel) h - hfs + hgs

end BoundaryWitness

end FiveTermDegreeTwo

end groupCohomology

theorem solution
    {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (H1 (Rep.res S.subtype A))] :
    Function.Injective
      (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using H2_induction_on with | h β =>
  simp only [H2π_comp_map_apply] at hx
  rw [H2π_eq_zero_iff] at hx
  obtain ⟨f, hf'⟩ := hx
  have hf : ∀ g h : G, A.ρ g (f h) - f (g * h) + f g = ↑(β ((g : G ⧸ S), (h : G ⧸ S))) := by
    intro g h
    have := congrFun hf' (g, h)
    rwa [d₁₂_hom_apply, coe_mapCocycles₂] at this
  have hc0 : H1π _ (restrictedCocycleOfInfBoundary β f hf) = 0 := Subsingleton.elim _ _
  rw [H1π_eq_zero_iff] at hc0
  obtain ⟨a, ha'⟩ := hc0
  have ha : ∀ s ∈ S, f s - f 1 = A.ρ s a - a := fun s hs => by
    have := congrFun ha' ⟨s, hs⟩
    rw [d₀₁_hom_apply, restrictedCocycleOfInfBoundary_apply] at this
    exact this.symm
  rw [H2π_eq_zero_iff]
  refine ⟨fun q => Quotient.liftOn' q
      (fun g => ⟨f g - (A.ρ g a - a),
        fun s => correctedCochain_mem_invariants β f hf a ha g s s.2⟩)
      (fun g₁ g₂ hg => Subtype.ext ?_),
    funext fun q => ?_⟩
  · have hS : g₁⁻¹ * g₂ ∈ S := QuotientGroup.leftRel_apply.mp hg
    have := correctedCochain_right_invariant β f hf a ha g₁ (g₁⁻¹ * g₂) hS
    simpa using this.symm
  · obtain ⟨q₁, q₂⟩ := q
    induction q₁ using QuotientGroup.induction_on with | H g₁ =>
    induction q₂ using QuotientGroup.induction_on with | H g₂ =>
    apply Subtype.ext
    show A.ρ g₁ (f g₂ - (A.ρ g₂ a - a)) - (f (g₁ * g₂) - (A.ρ (g₁ * g₂) a - a))
        + (f g₁ - (A.ρ g₁ a - a)) = ↑(β ((g₁ : G ⧸ S), (g₂ : G ⧸ S)))
    rw [map_sub, map_sub, show (A.ρ g₁) ((A.ρ g₂) a) = A.ρ (g₁ * g₂) a by rw [map_mul]; rfl]
    linear_combination (norm := abel) hf g₁ g₂

end S_groupCohomology_H2inf_injective_of_subsingleton_H1_res
end P2MW
export P2MW.S_groupCohomology_H2inf_injective_of_subsingleton_H1_res (solution)
