-- Prove2me | solution 1 for groupCohomology.bijective_theta_coind
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/7a677022-155e-543e-8374-6992351b23e0

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality

import Theorems.Thm_groupCohomology_coind_cocycles1_mem_coboundaries1_of_eval_one_mem_coboundaries1
import Theorems.Thm_groupCohomology_coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_exists_coind_cocycles1_isLevelConstant1_eval_one_eq
import Theorems.Thm_groupCohomology_exists_coind_mem_levelCocycles2_eval_one_eq
import Theorems.Thm_Rep_exists_level_coind_apply_eq_self
import Theorems.Thm_groupCohomology_cupCochain_coind_apply_one
import Theorems.Thm_groupCohomology_cup_mem_levelCocycles2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_bijective_theta_coind

set_option autoImplicit false
set_option maxHeartbeats 3200000

universe u

open CategoryTheory groupCohomology

namespace ShapiroTransport
open groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (U : Subgroup G)

noncomputable def ev (X : Rep.{u} k U) : Rep.coind U.subtype X →ₗ[k] X :=
  (LinearMap.proj (1 : G)).comp (Representation.coindV U.subtype X.ρ).subtype

lemma ev_apply (X : Rep.{u} k U) (c : Rep.coind U.subtype X) : ev U X c = (c : G → X) 1 := rfl

lemma coind_ρ_apply (X : Rep.{u} k U) (g h : G) (c : Rep.coind U.subtype X) :
    ((Rep.coind U.subtype X).ρ g c : G → X) h = (c : G → X) (h * g) := rfl

lemma coind_mem (X : Rep.{u} k U) (c : Rep.coind U.subtype X) (u : U) (h : G) :
    (c : G → X) (u * h) = X.ρ u ((c : G → X) h) := c.2 u h

lemma hev (X : Rep.{u} k U) (u : U) (c : Rep.coind U.subtype X) :
    ev U X ((Rep.coind U.subtype X).ρ (U.subtype u) c) = X.ρ u (ev U X c) := by
  rw [ev_apply, ev_apply, coind_ρ_apply, one_mul]
  have := coind_mem U X c u 1
  rw [mul_one] at this
  exact this

noncomputable def evHom (X : Rep.{u} k U) : Rep.res U.subtype (Rep.coind U.subtype X) ⟶ X :=
  Rep.ofHom ((ev U X).intertwiningMap_of_isIntertwiningMap
    (Rep.res U.subtype (Rep.coind U.subtype X)).ρ X.ρ (fun u c => hev U X u c))

variable (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

noncomputable def lcU (X : Rep.{u} k U) : levelCocycles₂ r (Rep.coind U.subtype X) →ₗ[k] levelCocycles₂ (r.comp U.subtype) X :=
  levelCocycles₂Map (rH := r) (rG := r.comp U.subtype) U.subtype (fun _ => rfl) (ev U X) (fun u c => hev U X u c)

noncomputable def sh2 (X : Rep.{u} k U) : continuousH2 r (Rep.coind U.subtype X) →ₗ[k] continuousH2 (r.comp U.subtype) X :=
  continuousH2Map (rH := r) (rG := r.comp U.subtype) U.subtype (fun _ => rfl) (ev U X) (fun u c => hev U X u c)

lemma sh2_π (X : Rep.{u} k U) (c : levelCocycles₂ r (Rep.coind U.subtype X)) :
    sh2 U r X (continuousH2π r _ c) = continuousH2π _ X (lcU U r X c) := rfl

lemma coe_lcU (X : Rep.{u} k U) (c : levelCocycles₂ r (Rep.coind U.subtype X)) (st : U × U) :
    (lcU U r X c : U × U → X) st = ((c : G × G → Rep.coind U.subtype X) ((st.1 : G), (st.2 : G)) : G → X) 1 := rfl

theorem sh2_bijective (X : Rep.{u} k U)
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ U) :
    Function.Bijective (sh2 U r X) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    induction y using Submodule.Quotient.induction_on with | _ c =>
    show continuousH2π r _ c = 0
    rw [continuousH2π_eq_zero_iff]
    apply groupCohomology.coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2 r U hU X c c.2
    have : continuousH2π _ X (lcU U r X c) = 0 := hy
    rw [continuousH2π_eq_zero_iff] at this
    exact this
  · intro y
    induction y using Submodule.Quotient.induction_on with | _ b =>
    obtain ⟨c, hc, hcb⟩ := groupCohomology.exists_coind_mem_levelCocycles2_eval_one_eq r U hU X b b.2
    refine ⟨continuousH2π r _ ⟨c, hc⟩, ?_⟩
    show continuousH2π _ X (lcU U r X ⟨c, hc⟩) = continuousH2π _ X b
    congr 1
    apply Subtype.ext
    funext st
    rw [coe_lcU]
    exact hcb st.1 st.2

lemma coe_mapCocycles₁_ev (X : Rep.{u} k U) (c : cocycles₁ (Rep.coind U.subtype X)) :
    (mapCocycles₁ U.subtype (evHom U X) c : U → X) = fun u : U => ((c (u : G) : Rep.coind U.subtype X) : G → X) 1 := rfl

lemma isLevelConstant₁_mapCocycles₁_ev (X : Rep.{u} k U) {c : cocycles₁ (Rep.coind U.subtype X)}
    (hc : IsLevelConstant₁ r c) : IsLevelConstant₁ (r.comp U.subtype) (mapCocycles₁ U.subtype (evHom U X) c) := by
  rw [coe_mapCocycles₁_ev]
  obtain ⟨F, hF, h⟩ := hc
  exact ⟨F, hF, fun g s hs => by
    show ((c ((g * s : U) : G) : Rep.coind U.subtype X) : G → X) 1 = ((c (g : G) : Rep.coind U.subtype X) : G → X) 1
    rw [Subgroup.coe_mul, h (g : G) (s : G) hs]⟩

lemma map_mem_continuousH1 (X : Rep.{u} k U) (x : continuousH1 r (Rep.coind U.subtype X)) :
    (map U.subtype (evHom U X) 1).hom (x : H1 (Rep.coind U.subtype X)) ∈ continuousH1 (r.comp U.subtype) X := by
  obtain ⟨c, hc, hx⟩ := (mem_continuousH1_iff r _ _).1 x.2
  rw [← hx, H1π_comp_map_apply]
  exact H1π_mem_continuousH1 _ X (isLevelConstant₁_mapCocycles₁_ev U r X hc)

noncomputable def sh1 (X : Rep.{u} k U) : continuousH1 r (Rep.coind U.subtype X) →ₗ[k] continuousH1 (r.comp U.subtype) X :=
  ((map U.subtype (evHom U X) 1).hom ∘ₗ (continuousH1 r _).subtype).codRestrict _ (map_mem_continuousH1 U r X)

lemma sh1_mk (X : Rep.{u} k U) (c : cocycles₁ (Rep.coind U.subtype X)) (hc : IsLevelConstant₁ r c) :
    sh1 U r X ⟨(H1π _).hom c, H1π_mem_continuousH1 r _ hc⟩
      = ⟨(H1π X).hom (mapCocycles₁ U.subtype (evHom U X) c),
          H1π_mem_continuousH1 _ X (isLevelConstant₁_mapCocycles₁_ev U r X hc)⟩ :=
  Subtype.ext (H1π_comp_map_apply U.subtype (evHom U X) c)

theorem sh1_bijective (X : Rep.{u} k U)
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ U) :
    Function.Bijective (sh1 U r X) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, hc, hcx⟩ := (mem_continuousH1_iff r _ _).1 x.2
    have hx0 : x = ⟨(H1π _).hom c, H1π_mem_continuousH1 r _ hc⟩ := Subtype.ext hcx.symm
    rw [hx0, sh1_mk U r X c hc] at hx
    have h1 : (H1π X).hom (mapCocycles₁ U.subtype (evHom U X) c) = 0 := Subtype.ext_iff.mp hx
    rw [H1π_eq_zero_iff, coe_mapCocycles₁_ev] at h1
    have h2 := groupCohomology.coind_cocycles1_mem_coboundaries1_of_eval_one_mem_coboundaries1 U X c h1
    rw [hx0]
    apply Subtype.ext
    show (H1π _).hom c = 0
    rw [H1π_eq_zero_iff]
    exact h2
  · intro y
    obtain ⟨b, hb, hby⟩ := (mem_continuousH1_iff _ X _).1 y.2
    obtain ⟨c, hc, hcb⟩ := groupCohomology.exists_coind_cocycles1_isLevelConstant1_eval_one_eq r U hU X b hb
    refine ⟨⟨(H1π _).hom c, H1π_mem_continuousH1 r _ hc⟩, ?_⟩
    rw [sh1_mk U r X c hc]
    apply Subtype.ext
    show (H1π X).hom (mapCocycles₁ U.subtype (evHom U X) c) = (y : H1 X)
    rw [← hby]
    congr 1
    apply cocycles₁_ext
    intro u
    rw [coe_mapCocycles₁_ev]
    exact hcb u

lemma coind_invariant_const (X : Rep.{u} k U) (m : (Rep.coind U.subtype X).ρ.invariants) (h : G) :
    ((m : Rep.coind U.subtype X) : G → X) h = ((m : Rep.coind U.subtype X) : G → X) 1 := by
  have := congrArg (fun c : Rep.coind U.subtype X => (c : G → X) 1) (m.2 h)
  simp only at this
  rw [coind_ρ_apply, one_mul] at this
  exact this

noncomputable def sh0 (X : Rep.{u} k U) : (Rep.coind U.subtype X).ρ.invariants →ₗ[k] X.ρ.invariants :=
  ((ev U X) ∘ₗ (Rep.coind U.subtype X).ρ.invariants.subtype).codRestrict _ fun m u => by
    show X.ρ u (((m : Rep.coind U.subtype X) : G → X) 1) = ((m : Rep.coind U.subtype X) : G → X) 1
    rw [← coind_mem, coind_invariant_const]

lemma coe_sh0 (X : Rep.{u} k U) (m : (Rep.coind U.subtype X).ρ.invariants) :
    (sh0 U X m : X) = ((m : Rep.coind U.subtype X) : G → X) 1 := rfl

theorem sh0_bijective (X : Rep.{u} k U) : Function.Bijective (sh0 U X) := by
  constructor
  · intro m m' h
    have h1 : ((m : Rep.coind U.subtype X) : G → X) 1 = ((m' : Rep.coind U.subtype X) : G → X) 1 := by
      rw [← coe_sh0, ← coe_sh0, h]
    apply Subtype.ext; apply Subtype.ext; funext g
    rw [coind_invariant_const U X m, coind_invariant_const U X m', h1]
  · intro x
    let c : Rep.coind U.subtype X := ⟨fun _ => (x : X), fun u h => (x.2 u).symm⟩
    refine ⟨⟨c, fun g => Subtype.ext (funext fun h => rfl)⟩, Subtype.ext rfl⟩

variable {U}
variable {NU DU : Rep.{u} k U} {Nμ : Rep.{u} k G}
  (φU : NU →ₗ[k] DU →ₗ[k] Rep.res U.subtype Nμ) (hφU : Rep.IsEquivariantBilinear NU DU (Rep.res U.subtype Nμ) φU)

include hφU in
lemma ptw_mem (f : Rep.coind U.subtype NU) (g : Rep.coind U.subtype DU) :
    (fun h : G => φU ((f : G → NU) h) ((g : G → DU) h)) ∈ Representation.coindV U.subtype (Rep.res U.subtype Nμ).ρ := by
  intro u h
  show φU ((f : G → NU) (u * h)) ((g : G → DU) (u * h)) = (Rep.res U.subtype Nμ).ρ u (φU ((f : G → NU) h) ((g : G → DU) h))
  rw [coind_mem, coind_mem, hφU]

noncomputable def ptw : Rep.coind U.subtype NU →ₗ[k] Rep.coind U.subtype DU →ₗ[k] Rep.coind U.subtype (Rep.res U.subtype Nμ) :=
  LinearMap.mk₂ k (fun f g => ⟨fun h : G => φU ((f : G → NU) h) ((g : G → DU) h), ptw_mem φU hφU f g⟩)
    (fun f f' g => by apply Subtype.ext; funext h; show φU ((f : G → NU) h + (f' : G → NU) h) _ = φU _ _ + φU _ _; rw [map_add, LinearMap.add_apply])
    (fun c f g => by apply Subtype.ext; funext h; show φU (c • (f : G → NU) h) _ = c • φU _ _; rw [map_smul, LinearMap.smul_apply])
    (fun f g g' => by apply Subtype.ext; funext h; show φU _ ((g : G → DU) h + (g' : G → DU) h) = φU _ _ + φU _ _; rw [map_add])
    (fun c f g => by apply Subtype.ext; funext h; show φU _ (c • (g : G → DU) h) = c • φU _ _; rw [map_smul])

lemma coe_ptw (f : Rep.coind U.subtype NU) (g : Rep.coind U.subtype DU) (h : G) :
    (ptw φU hφU f g : G → Nμ) h = φU ((f : G → NU) h) ((g : G → DU) h) := rfl

theorem ptw_equivariant :
    Rep.IsEquivariantBilinear (Rep.coind U.subtype NU) (Rep.coind U.subtype DU) (Rep.coind U.subtype (Rep.res U.subtype Nμ))
      (ptw φU hφU) := by
  intro g f d
  apply Subtype.ext
  funext h
  rfl

end ShapiroTransport

theorem solution
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (U : Subgroup G) [U.FiniteIndex]
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ U)
    {NU DU : Rep.{u} k U} {Nμ : Rep.{u} k G}
    (φU : NU →ₗ[k] DU →ₗ[k] Rep.res U.subtype Nμ) (hφU : Rep.IsEquivariantBilinear NU DU (Rep.res U.subtype Nμ) φU)
    (hsmDU : ∀ x : DU, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : U, (r.comp U.subtype) s ∈ F.fixingSubgroup → DU.ρ s x = x)
    (invU : continuousH2 (r.comp U.subtype) (Rep.res U.subtype Nμ) →ₗ[k] k) (invG : continuousH2 r Nμ →ₗ[k] k)
    (τ : Rep.coind U.subtype (Rep.res U.subtype Nμ) ⟶ Nμ)
    (hinv : ∀ (w : levelCocycles₂ r (Rep.coind U.subtype (Rep.res U.subtype Nμ)))
      (w₁ : levelCocycles₂ (r.comp U.subtype) (Rep.res U.subtype Nμ)),
      (∀ s t : U, (w₁ : U × U → Nμ) (s, t)
        = ((w : G × G → Rep.coind U.subtype (Rep.res U.subtype Nμ)) ((s : G), (t : G)) : G → Nμ) 1) →
      invG (continuousH2MapHom r τ (continuousH2π r _ w)) = invU (continuousH2π _ _ w₁))
    (Ψ : Rep.coind U.subtype NU →ₗ[k] Rep.coind U.subtype DU →ₗ[k] Nμ)
    (hΨ : ∀ (f : Rep.coind U.subtype NU) (g : Rep.coind U.subtype DU) (w : Rep.coind U.subtype (Rep.res U.subtype Nμ)),
      (∀ h : G, (w : G → Nμ) h = φU ((f : G → NU) h) ((g : G → DU) h)) → Ψ f g = τ.hom w)
    (θ₀ : NU.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 (r.comp U.subtype) DU)) (hθ₀ : IsTheta0 (r.comp U.subtype) φU invU θ₀)
    (θ₁ : continuousH1 (r.comp U.subtype) NU →ₗ[k] Module.Dual k (continuousH1 (r.comp U.subtype) DU))
    (hθ₁ : IsTheta1 (r.comp U.subtype) φU invU θ₁)
    (θ₂ : continuousH2 (r.comp U.subtype) NU →ₗ[k] Module.Dual k DU.ρ.invariants) (hθ₂ : IsTheta2 (r.comp U.subtype) φU invU θ₂)
    (Θ₀ : (Rep.coind U.subtype NU).ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r (Rep.coind U.subtype DU)))
    (hΘ₀ : IsTheta0 r Ψ invG Θ₀)
    (Θ₁ : continuousH1 r (Rep.coind U.subtype NU) →ₗ[k] Module.Dual k (continuousH1 r (Rep.coind U.subtype DU)))
    (hΘ₁ : IsTheta1 r Ψ invG Θ₁)
    (Θ₂ : continuousH2 r (Rep.coind U.subtype NU) →ₗ[k] Module.Dual k (Rep.coind U.subtype DU).ρ.invariants)
    (hΘ₂ : IsTheta2 r Ψ invG Θ₂)
    (hU' : Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂) :
    Function.Bijective Θ₀ ∧ Function.Bijective Θ₁ ∧ Function.Bijective Θ₂ := by
  classical
  obtain ⟨hb₀, hb₁, hb₂⟩ := hU'

  have hsmC : ∀ b : Rep.coind U.subtype DU, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → (Rep.coind U.subtype DU).ρ s b = b :=
    fun b => Rep.exists_level_coind_apply_eq_self r U hU DU hsmDU b

  let Φ := ShapiroTransport.ptw φU hφU
  have hΦ := ShapiroTransport.ptw_equivariant φU hφU
  have hΨΦ : ∀ (f : Rep.coind U.subtype NU) (g : Rep.coind U.subtype DU), Ψ f g = τ.hom (Φ f g) :=
    fun f g => hΨ f g (Φ f g) (fun _ => rfl)

  let lcτ : levelCocycles₂ r (Rep.coind U.subtype (Rep.res U.subtype Nμ)) →ₗ[k] levelCocycles₂ r Nμ :=
    levelCocycles₂Map (MonoidHom.id G) (fun _ => rfl) τ.hom.toLinearMap (fun g a => Rep.hom_comm_apply τ g a)
  have hlcτ : ∀ W, continuousH2MapHom r τ (continuousH2π r _ W) = continuousH2π r Nμ (lcτ W) := fun _ => rfl

  let S0N := ShapiroTransport.sh0 U NU
  let S0D := ShapiroTransport.sh0 U DU
  let S1N := ShapiroTransport.sh1 U r NU
  let S1D := ShapiroTransport.sh1 U r DU
  let S2N := ShapiroTransport.sh2 U r NU
  let S2D := ShapiroTransport.sh2 U r DU
  have hS0N := ShapiroTransport.sh0_bijective U NU
  have hS0D := ShapiroTransport.sh0_bijective U DU
  have hS1N := ShapiroTransport.sh1_bijective U r NU hU
  have hS1D := ShapiroTransport.sh1_bijective U r DU hU
  have hS2N := ShapiroTransport.sh2_bijective U r NU hU
  have hS2D := ShapiroTransport.sh2_bijective U r DU hU

  have H0 : ∀ (m : (Rep.coind U.subtype NU).ρ.invariants) (y : continuousH2 r (Rep.coind U.subtype DU)),
      Θ₀ m y = θ₀ (S0N m) (S2D y) := by
    intro m y
    induction y using Submodule.Quotient.induction_on with | _ z =>
    let W : levelCocycles₂ r (Rep.coind U.subtype (Rep.res U.subtype Nμ)) :=
      levelCocycles₂Map (MonoidHom.id G) (fun _ => rfl) (Φ (m : Rep.coind U.subtype NU)) (fun g b => by
        show Φ (m : Rep.coind U.subtype NU) ((Rep.coind U.subtype DU).ρ g b) = (Rep.coind U.subtype (Rep.res U.subtype Nμ)).ρ g (Φ m b)
        conv_lhs => rw [← m.2 g]
        exact hΦ g m b) z
    let w₁ := ShapiroTransport.lcU U r (Rep.res U.subtype Nμ) W
    have h1 : Θ₀ m (continuousH2π r _ z) = invG (continuousH2π r Nμ (lcτ W)) :=
      hΘ₀ m z (lcτ W) (fun st => by
        show τ.hom (Φ (m : Rep.coind U.subtype NU) ((z : G × G → Rep.coind U.subtype DU) st)) = Ψ (m : Rep.coind U.subtype NU) _
        rw [hΨΦ])
    have h2 : invG (continuousH2π r Nμ (lcτ W)) = invU (continuousH2π _ _ w₁) := hinv W w₁ (fun s t => rfl)
    have h3 : θ₀ (S0N m) (S2D (continuousH2π r _ z)) = invU (continuousH2π _ _ w₁) :=
      hθ₀ (S0N m) (ShapiroTransport.lcU U r DU z) w₁ (fun st => rfl)
    exact h1.trans (h2.trans h3.symm)

  have H2 : ∀ (y : continuousH2 r (Rep.coind U.subtype NU)) (d : (Rep.coind U.subtype DU).ρ.invariants),
      Θ₂ y d = θ₂ (S2N y) (S0D d) := by
    intro y d
    induction y using Submodule.Quotient.induction_on with | _ z =>
    let W : levelCocycles₂ r (Rep.coind U.subtype (Rep.res U.subtype Nμ)) :=
      levelCocycles₂Map (MonoidHom.id G) (fun _ => rfl) (Φ.flip (d : Rep.coind U.subtype DU)) (fun g a => by
        show Φ ((Rep.coind U.subtype NU).ρ g a) (d : Rep.coind U.subtype DU) = (Rep.coind U.subtype (Rep.res U.subtype Nμ)).ρ g (Φ a d)
        conv_lhs => rw [← d.2 g]
        exact hΦ g a d) z
    let w₁ := ShapiroTransport.lcU U r (Rep.res U.subtype Nμ) W
    have h1 : Θ₂ (continuousH2π r _ z) d = invG (continuousH2π r Nμ (lcτ W)) :=
      hΘ₂ z d (lcτ W) (fun st => by
        show τ.hom (Φ ((z : G × G → Rep.coind U.subtype NU) st) (d : Rep.coind U.subtype DU)) = Ψ _ (d : Rep.coind U.subtype DU)
        rw [hΨΦ])
    have h2 : invG (continuousH2π r Nμ (lcτ W)) = invU (continuousH2π _ _ w₁) := hinv W w₁ (fun s t => rfl)
    have h3 : θ₂ (S2N (continuousH2π r _ z)) (S0D d) = invU (continuousH2π _ _ w₁) :=
      hθ₂ (ShapiroTransport.lcU U r NU z) (S0D d) w₁ (fun st => rfl)
    exact h1.trans (h2.trans h3.symm)

  have H1 : ∀ (x : continuousH1 r (Rep.coind U.subtype NU)) (y : continuousH1 r (Rep.coind U.subtype DU)),
      Θ₁ x y = θ₁ (S1N x) (S1D y) := by
    intro x y
    obtain ⟨f, hf, hfx⟩ := (mem_continuousH1_iff r _ _).1 x.2
    obtain ⟨g, hg, hgy⟩ := (mem_continuousH1_iff r _ _).1 y.2
    have hx : x = ⟨(H1π _).hom f, H1π_mem_continuousH1 r _ hf⟩ := Subtype.ext hfx.symm
    have hy : y = ⟨(H1π _).hom g, H1π_mem_continuousH1 r _ hg⟩ := Subtype.ext hgy.symm
    subst hx; subst hy
    let W : levelCocycles₂ r (Rep.coind U.subtype (Rep.res U.subtype Nμ)) := ⟨cupCochain Φ (⇑f) (⇑g), by
      rw [← cup_coe Φ hΦ]
      exact groupCohomology.cup_mem_levelCocycles2 r Φ hΦ hsmC f g hf hg⟩
    let w₁ := ShapiroTransport.lcU U r (Rep.res U.subtype Nμ) W
    have h1 : Θ₁ ⟨(H1π _).hom f, H1π_mem_continuousH1 r _ hf⟩ ⟨(H1π _).hom g, H1π_mem_continuousH1 r _ hg⟩
        = invG (continuousH2π r Nμ (lcτ W)) :=
      hΘ₁ f hf g hg (lcτ W) (fun st => by
        show τ.hom (Φ (f st.1) ((Rep.coind U.subtype DU).ρ st.1 (g st.2))) = Ψ (f st.1) ((Rep.coind U.subtype DU).ρ st.1 (g st.2))
        rw [hΨΦ])
    have h2 : invG (continuousH2π r Nμ (lcτ W)) = invU (continuousH2π _ _ w₁) := hinv W w₁ (fun s t => rfl)
    have h3 : θ₁ (S1N ⟨(H1π _).hom f, H1π_mem_continuousH1 r _ hf⟩) (S1D ⟨(H1π _).hom g, H1π_mem_continuousH1 r _ hg⟩)
        = invU (continuousH2π _ _ w₁) := by
      show θ₁ (ShapiroTransport.sh1 U r NU _) (ShapiroTransport.sh1 U r DU _) = _
      rw [ShapiroTransport.sh1_mk U r NU f hf, ShapiroTransport.sh1_mk U r DU g hg]
      refine hθ₁ _ (ShapiroTransport.isLevelConstant₁_mapCocycles₁_ev U r NU hf) _
        (ShapiroTransport.isLevelConstant₁_mapCocycles₁_ev U r DU hg) w₁ (fun st => ?_)
      obtain ⟨s, t⟩ := st
      exact groupCohomology.cupCochain_coind_apply_one U φU (⇑f) (⇑g) s t
    exact h1.trans (h2.trans h3.symm)

  let e2D := LinearEquiv.ofBijective S2D hS2D
  let e0D := LinearEquiv.ofBijective S0D hS0D
  let e1D := LinearEquiv.ofBijective S1D hS1D
  have E0 : (⇑Θ₀) = ⇑e2D.dualMap ∘ ⇑θ₀ ∘ ⇑S0N := by
    funext m
    apply LinearMap.ext
    intro y
    show Θ₀ m y = e2D.dualMap (θ₀ (S0N m)) y
    rw [LinearEquiv.dualMap_apply]
    exact H0 m y
  have E2 : (⇑Θ₂) = ⇑e0D.dualMap ∘ ⇑θ₂ ∘ ⇑S2N := by
    funext y
    apply LinearMap.ext
    intro d
    show Θ₂ y d = e0D.dualMap (θ₂ (S2N y)) d
    rw [LinearEquiv.dualMap_apply]
    exact H2 y d
  have E1 : (⇑Θ₁) = ⇑e1D.dualMap ∘ ⇑θ₁ ∘ ⇑S1N := by
    funext x
    apply LinearMap.ext
    intro y
    show Θ₁ x y = e1D.dualMap (θ₁ (S1N x)) y
    rw [LinearEquiv.dualMap_apply]
    exact H1 x y
  refine ⟨?_, ?_, ?_⟩
  · rw [E0]; exact e2D.dualMap.bijective.comp (hb₀.comp hS0N)
  · rw [E1]; exact e1D.dualMap.bijective.comp (hb₁.comp hS1N)
  · rw [E2]; exact e0D.dualMap.bijective.comp (hb₂.comp hS2N)

end S_groupCohomology_bijective_theta_coind
end P2MW
export P2MW.S_groupCohomology_bijective_theta_coind (solution)
