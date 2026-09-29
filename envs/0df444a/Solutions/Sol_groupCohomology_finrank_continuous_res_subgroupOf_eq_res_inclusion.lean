-- Prove2me | solution 1 for groupCohomology.finrank_continuous_res_subgroupOf_eq_res_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c410756a-ad68-52bd-aac9-e35a5833faa0

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_continuous_res_subgroupOf_eq_res_inclusion

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory

open groupCohomology in
theorem solution {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S' S : Subgroup G) (hle : S' ≤ S) (N : Rep.{u} k S) :
    Module.finrank k (Rep.res (S'.subgroupOf S).subtype N).ρ.invariants
        = Module.finrank k (Rep.res (Subgroup.inclusion hle) N).ρ.invariants ∧
    Module.finrank k (groupCohomology.continuousH1 ((r.comp S.subtype).comp (S'.subgroupOf S).subtype)
          (Rep.res (S'.subgroupOf S).subtype N))
        = Module.finrank k (groupCohomology.continuousH1 (r.comp S'.subtype) (Rep.res (Subgroup.inclusion hle) N)) ∧
    Module.finrank k (groupCohomology.continuousH2 ((r.comp S.subtype).comp (S'.subgroupOf S).subtype)
          (Rep.res (S'.subgroupOf S).subtype N))
        = Module.finrank k (groupCohomology.continuousH2 (r.comp S'.subtype) (Rep.res (Subgroup.inclusion hle) N)) := by
  classical

  let H₁ := S'.subgroupOf S
  let N₁ : Rep.{u} k H₁ := Rep.res H₁.subtype N
  let N₂ : Rep.{u} k S' := Rep.res (Subgroup.inclusion hle) N
  let r₁ : H₁ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := (r.comp S.subtype).comp H₁.subtype
  let r₂ : S' →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := r.comp S'.subtype
  let e : H₁ ≃* S' := Subgroup.subgroupOfEquivOfLe hle
  have he : ∀ g : H₁, r₂ (e g) = r₁ g := fun _ => rfl
  have he' : ∀ y : S', r₁ (e.symm y) = r₂ y := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    have : N₁.ρ.invariants = N₂.ρ.invariants := by
      ext v
      simp only [Representation.mem_invariants]
      constructor
      · intro h y; exact h (e.symm y)
      · intro h x; exact h (e x)
    show Module.finrank k N₁.ρ.invariants = Module.finrank k N₂.ρ.invariants
    rw [this]
  ·
    let φ : Rep.res e.toMonoidHom N₂ ⟶ N₁ :=
      Rep.ofHom ((LinearMap.id : N →ₗ[k] N).intertwiningMap_of_isIntertwiningMap
        (Rep.res e.toMonoidHom N₂).ρ N₁.ρ (fun _ _ => rfl))
    let ψ : Rep.res e.symm.toMonoidHom N₁ ⟶ N₂ :=
      Rep.ofHom ((LinearMap.id : N →ₗ[k] N).intertwiningMap_of_isIntertwiningMap
        (Rep.res e.symm.toMonoidHom N₁).ρ N₂.ρ (fun _ _ => rfl))
    have cφ : ∀ c : cocycles₁ N₂, (mapCocycles₁ e.toMonoidHom φ c : H₁ → N) = fun g => c (e g) := fun _ => rfl
    have cψ : ∀ c : cocycles₁ N₁, (mapCocycles₁ e.symm.toMonoidHom ψ c : S' → N) = fun y => c (e.symm y) :=
      fun _ => rfl
    have Hφ : ∀ c : cocycles₁ N₂, (map e.toMonoidHom φ 1).hom ((H1π N₂).hom c)
        = (H1π N₁).hom (mapCocycles₁ e.toMonoidHom φ c) := fun c => H1π_comp_map_apply _ _ c
    have Hψ : ∀ c : cocycles₁ N₁, (map e.symm.toMonoidHom ψ 1).hom ((H1π N₁).hom c)
        = (H1π N₂).hom (mapCocycles₁ e.symm.toMonoidHom ψ c) := fun c => H1π_comp_map_apply _ _ c
    have mφ : ∀ x : continuousH1 r₂ N₂, (map e.toMonoidHom φ 1).hom (x : H1 N₂) ∈ continuousH1 r₁ N₁ := by
      intro x
      obtain ⟨c, ⟨F, hF, hc⟩, hx⟩ := (mem_continuousH1_iff r₂ N₂ _).1 x.2
      rw [← hx, Hφ]
      exact H1π_mem_continuousH1 r₁ N₁ ⟨F, hF, fun g s hs => by
        rw [cφ]; show c (e (g * s)) = c (e g); rw [map_mul]; exact hc (e g) (e s) hs⟩
    have mψ : ∀ x : continuousH1 r₁ N₁, (map e.symm.toMonoidHom ψ 1).hom (x : H1 N₁) ∈ continuousH1 r₂ N₂ := by
      intro x
      obtain ⟨c, ⟨F, hF, hc⟩, hx⟩ := (mem_continuousH1_iff r₁ N₁ _).1 x.2
      rw [← hx, Hψ]
      exact H1π_mem_continuousH1 r₂ N₂ ⟨F, hF, fun g s hs => by
        rw [cψ]; show c (e.symm (g * s)) = c (e.symm g); rw [map_mul]; exact hc (e.symm g) (e.symm s) hs⟩
    let Φ : continuousH1 r₂ N₂ →ₗ[k] continuousH1 r₁ N₁ :=
      ((map e.toMonoidHom φ 1).hom ∘ₗ (continuousH1 r₂ N₂).subtype).codRestrict _ mφ
    let Ψ : continuousH1 r₁ N₁ →ₗ[k] continuousH1 r₂ N₂ :=
      ((map e.symm.toMonoidHom ψ 1).hom ∘ₗ (continuousH1 r₁ N₁).subtype).codRestrict _ mψ
    have h1 : ∀ x, Φ (Ψ x) = x := by
      intro x
      obtain ⟨c, -, hx⟩ := (mem_continuousH1_iff r₁ N₁ _).1 x.2
      apply Subtype.ext
      show (map e.toMonoidHom φ 1).hom ((map e.symm.toMonoidHom ψ 1).hom (x : H1 N₁)) = x
      rw [← hx, Hψ, Hφ]
      congr 1
      all_goals
        apply cocycles₁_ext
        intro g
        exact ((congrFun (cφ _) g).trans (congrFun (cψ c) (e g))).trans (congrArg c (e.symm_apply_apply g))
    have h2 : ∀ x, Ψ (Φ x) = x := by
      intro x
      obtain ⟨c, -, hx⟩ := (mem_continuousH1_iff r₂ N₂ _).1 x.2
      apply Subtype.ext
      show (map e.symm.toMonoidHom ψ 1).hom ((map e.toMonoidHom φ 1).hom (x : H1 N₂)) = x
      rw [← hx, Hφ, Hψ]
      congr 1
      all_goals
        apply cocycles₁_ext
        intro y
        exact ((congrFun (cψ _) y).trans (congrFun (cφ c) (e.symm y))).trans (congrArg c (e.apply_symm_apply y))
    exact (LinearEquiv.ofLinear Ψ Φ (LinearMap.ext h2) (LinearMap.ext h1)).finrank_eq
  ·
    let Φ : continuousH2 r₂ N₂ →ₗ[k] continuousH2 r₁ N₁ :=
      continuousH2Map e.toMonoidHom he (LinearMap.id : N →ₗ[k] N) (fun _ _ => rfl)
    let Ψ : continuousH2 r₁ N₁ →ₗ[k] continuousH2 r₂ N₂ :=
      continuousH2Map e.symm.toMonoidHom he' (LinearMap.id : N →ₗ[k] N) (fun _ _ => rfl)
    have h1 : ∀ z, Φ (Ψ z) = z := by
      intro z
      induction z using Submodule.Quotient.induction_on with | _ x =>
      change continuousH2π r₁ N₁ _ = continuousH2π r₁ N₁ x
      congr 1
      all_goals
        apply Subtype.ext
        funext p
        change (x : H₁ × H₁ → N) (e.symm (e p.1), e.symm (e p.2)) = (x : H₁ × H₁ → N) p
        simp only [MulEquiv.symm_apply_apply, Prod.mk.eta]
    have h2 : ∀ z, Ψ (Φ z) = z := by
      intro z
      induction z using Submodule.Quotient.induction_on with | _ x =>
      change continuousH2π r₂ N₂ _ = continuousH2π r₂ N₂ x
      congr 1
      all_goals
        apply Subtype.ext
        funext p
        change (x : S' × S' → N) (e (e.symm p.1), e (e.symm p.2)) = (x : S' × S' → N) p
        simp only [MulEquiv.apply_symm_apply, Prod.mk.eta]
    exact (LinearEquiv.ofLinear Ψ Φ (LinearMap.ext h2) (LinearMap.ext h1)).finrank_eq

end S_groupCohomology_finrank_continuous_res_subgroupOf_eq_res_inclusion
end P2MW
export P2MW.S_groupCohomology_finrank_continuous_res_subgroupOf_eq_res_inclusion (solution)
