-- Prove2me | solution 1 for groupCohomology.nonempty_continuous_linearEquiv_of_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/5063a142-3fbc-513e-b608-f32737932e7e

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory

open groupCohomology in
theorem solution {k G H : Type u} [CommRing k] [Group G] [Group H]
    (rG : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (rH : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (e : G ≃* H) (he : ∀ g, rH (e g) = rG g) (NG : Rep.{u} k G) (NH : Rep.{u} k H)
    (φ : NG ≃ₗ[k] NH) (hφ : ∀ (g : G) (x : NG), φ (NG.ρ g x) = NH.ρ (e g) (φ x)) :
    Nonempty (NG.ρ.invariants ≃ₗ[k] NH.ρ.invariants) ∧
    Nonempty (groupCohomology.continuousH1 rG NG ≃ₗ[k] groupCohomology.continuousH1 rH NH) ∧
    Nonempty (groupCohomology.continuousH2 rG NG ≃ₗ[k] groupCohomology.continuousH2 rH NH) := by
  classical
  have he' : ∀ h : H, rG (e.symm h) = rH h := fun h => by rw [← he, MulEquiv.apply_symm_apply]

  have hφ' : ∀ (h : H) (y : NH), φ.symm (NH.ρ h y) = NG.ρ (e.symm h) (φ.symm y) := by
    intro h y
    apply φ.injective
    rw [hφ, MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

  have hφG : ∀ (g : G) (y : NH), φ.symm (NH.ρ (e g) y) = NG.ρ g (φ.symm y) := by
    intro g y; rw [hφ', MulEquiv.symm_apply_apply]
  have hφH : ∀ (h : H) (x : NG), φ (NG.ρ (e.symm h) x) = NH.ρ h (φ x) := by
    intro h x; rw [hφ, MulEquiv.apply_symm_apply]
  refine ⟨?_, ?_, ?_⟩
  ·
    have m₁ : ∀ x : NG.ρ.invariants, φ (x : NG) ∈ NH.ρ.invariants := by
      intro x
      rw [Representation.mem_invariants]
      intro h
      rw [← hφH, x.2 (e.symm h)]
    have m₂ : ∀ y : NH.ρ.invariants, φ.symm (y : NH) ∈ NG.ρ.invariants := by
      intro y
      rw [Representation.mem_invariants]
      intro g
      rw [← hφG, y.2 (e g)]
    refine ⟨LinearEquiv.ofLinear
      ((φ.toLinearMap ∘ₗ NG.ρ.invariants.subtype).codRestrict NH.ρ.invariants m₁)
      ((φ.symm.toLinearMap ∘ₗ NH.ρ.invariants.subtype).codRestrict NG.ρ.invariants m₂) ?_ ?_⟩
    · apply LinearMap.ext; intro y; apply Subtype.ext
      simp
    · apply LinearMap.ext; intro x; apply Subtype.ext
      simp
  ·
    let ψH : Rep.res e.symm.toMonoidHom NG ⟶ NH :=
      Rep.ofHom (φ.toLinearMap.intertwiningMap_of_isIntertwiningMap
        (Rep.res e.symm.toMonoidHom NG).ρ NH.ρ (fun h x => hφH h x))
    let ψG : Rep.res e.toMonoidHom NH ⟶ NG :=
      Rep.ofHom (φ.symm.toLinearMap.intertwiningMap_of_isIntertwiningMap
        (Rep.res e.toMonoidHom NH).ρ NG.ρ (fun g y => hφG g y))
    have cH : ∀ c : cocycles₁ NG, (mapCocycles₁ e.symm.toMonoidHom ψH c : H → NH) = fun h => φ (c (e.symm h)) :=
      fun _ => rfl
    have cG : ∀ c : cocycles₁ NH, (mapCocycles₁ e.toMonoidHom ψG c : G → NG) = fun g => φ.symm (c (e g)) :=
      fun _ => rfl
    have HH : ∀ c : cocycles₁ NG, (map e.symm.toMonoidHom ψH 1).hom ((H1π NG).hom c)
        = (H1π NH).hom (mapCocycles₁ e.symm.toMonoidHom ψH c) := fun c => H1π_comp_map_apply _ _ c
    have HG : ∀ c : cocycles₁ NH, (map e.toMonoidHom ψG 1).hom ((H1π NH).hom c)
        = (H1π NG).hom (mapCocycles₁ e.toMonoidHom ψG c) := fun c => H1π_comp_map_apply _ _ c
    have mH : ∀ x : continuousH1 rG NG, (map e.symm.toMonoidHom ψH 1).hom (x : H1 NG) ∈ continuousH1 rH NH := by
      intro x
      obtain ⟨c, ⟨F, hF, hc⟩, hx⟩ := (mem_continuousH1_iff rG NG _).1 x.2
      rw [← hx, HH]
      exact H1π_mem_continuousH1 rH NH ⟨F, hF, fun g s hs => by
        rw [cH]; show φ (c (e.symm (g * s))) = φ (c (e.symm g))
        rw [map_mul, hc (e.symm g) (e.symm s) (by rw [he']; exact hs)]⟩
    have mG : ∀ x : continuousH1 rH NH, (map e.toMonoidHom ψG 1).hom (x : H1 NH) ∈ continuousH1 rG NG := by
      intro x
      obtain ⟨c, ⟨F, hF, hc⟩, hx⟩ := (mem_continuousH1_iff rH NH _).1 x.2
      rw [← hx, HG]
      exact H1π_mem_continuousH1 rG NG ⟨F, hF, fun g s hs => by
        rw [cG]; show φ.symm (c (e (g * s))) = φ.symm (c (e g))
        rw [map_mul, hc (e g) (e s) (by rw [he]; exact hs)]⟩
    let Φ : continuousH1 rG NG →ₗ[k] continuousH1 rH NH :=
      ((map e.symm.toMonoidHom ψH 1).hom ∘ₗ (continuousH1 rG NG).subtype).codRestrict _ mH
    let Ψ : continuousH1 rH NH →ₗ[k] continuousH1 rG NG :=
      ((map e.toMonoidHom ψG 1).hom ∘ₗ (continuousH1 rH NH).subtype).codRestrict _ mG
    have h1 : ∀ x, Φ (Ψ x) = x := by
      intro x
      obtain ⟨c, -, hx⟩ := (mem_continuousH1_iff rH NH _).1 x.2
      apply Subtype.ext
      show (map e.symm.toMonoidHom ψH 1).hom ((map e.toMonoidHom ψG 1).hom (x : H1 NH)) = x
      rw [← hx, HG, HH]
      congr 1
      apply cocycles₁_ext
      intro h
      rw [cH]
      show φ ((mapCocycles₁ e.toMonoidHom ψG c : G → NG) (e.symm h)) = c h
      rw [cG]
      show φ (φ.symm (c (e (e.symm h)))) = c h
      rw [LinearEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have h2 : ∀ x, Ψ (Φ x) = x := by
      intro x
      obtain ⟨c, -, hx⟩ := (mem_continuousH1_iff rG NG _).1 x.2
      apply Subtype.ext
      show (map e.toMonoidHom ψG 1).hom ((map e.symm.toMonoidHom ψH 1).hom (x : H1 NG)) = x
      rw [← hx, HH, HG]
      congr 1
      apply cocycles₁_ext
      intro g
      rw [cG]
      show φ.symm ((mapCocycles₁ e.symm.toMonoidHom ψH c : H → NH) (e g)) = c g
      rw [cH]
      show φ.symm (φ (c (e.symm (e g)))) = c g
      rw [LinearEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact ⟨LinearEquiv.ofLinear Φ Ψ (LinearMap.ext h1) (LinearMap.ext h2)⟩
  ·
    let Φ : continuousH2 rG NG →ₗ[k] continuousH2 rH NH :=
      continuousH2Map e.symm.toMonoidHom he' φ.toLinearMap (fun h x => hφH h x)
    let Ψ : continuousH2 rH NH →ₗ[k] continuousH2 rG NG :=
      continuousH2Map e.toMonoidHom he φ.symm.toLinearMap (fun g y => hφG g y)
    have h1 : ∀ z, Φ (Ψ z) = z := by
      intro z
      induction z using Submodule.Quotient.induction_on with | _ x =>
      change continuousH2π rH NH _ = continuousH2π rH NH x
      congr 1
      apply Subtype.ext
      funext p
      change φ (φ.symm ((x : H × H → NH) (e (e.symm p.1), e (e.symm p.2)))) = (x : H × H → NH) p
      simp only [LinearEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, Prod.mk.eta]
    have h2 : ∀ z, Ψ (Φ z) = z := by
      intro z
      induction z using Submodule.Quotient.induction_on with | _ x =>
      change continuousH2π rG NG _ = continuousH2π rG NG x
      congr 1
      apply Subtype.ext
      funext p
      change φ.symm (φ ((x : G × G → NG) (e.symm (e p.1), e.symm (e p.2)))) = (x : G × G → NG) p
      simp only [LinearEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, Prod.mk.eta]
    exact ⟨LinearEquiv.ofLinear Φ Ψ (LinearMap.ext h1) (LinearMap.ext h2)⟩

end S_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv
end P2MW
export P2MW.S_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv (solution)
