-- Prove2me | solution 1 for groupCohomology.bijective_theta_dualTwist_of_res
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/adce4f05-6d3e-50a4-a402-a9c9eba1d63b

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_Rep_exists_hom_coind_res_comp_eq_index_smul
import Theorems.Thm_Rep_isEquivariantBilinear_eval_dualTwist
import Theorems.Thm_Rep_dualTwist_smooth
import Theorems.Thm_groupCohomology_exists_theta0_and_theta2
import Theorems.Thm_groupCohomology_exists_theta1
import Theorems.Thm_groupCohomology_bijective_theta_of_retract
import Theorems.Thm_groupCohomology_bijective_theta_coind
import Theorems.Thm_Rep_coind_pairing_adjoint
import Theorems.Thm_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_isOpen
import Theorems.Thm_groupCohomology_exists_level_ofChar_cycloChar_comp
import Theorems.Thm_Rep_exists_level_coind_apply_eq_self
import Theorems.Thm_groupCohomology_coind_cocycles1_mem_coboundaries1_of_eval_one_mem_coboundaries1
import Theorems.Thm_groupCohomology_coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_exists_coind_cocycles1_isLevelConstant1_eval_one_eq
import Theorems.Thm_groupCohomology_exists_coind_mem_levelCocycles2_eval_one_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_bijective_theta_dualTwist_of_res
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u
open CategoryTheory Module groupCohomology ExtCitation

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
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q)) [S.FiniteIndex] (hSp : IsUnit ((S.index : ℕ) : ZMod p))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
    (hres : ∀ (invS : continuousH2 ((primeLocalToGlobal q).comp S.subtype)
        (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p),
      Function.Bijective invS →
      ∀ (θ₀ : (Rep.res S.subtype M).ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))),
        IsTheta0 ((primeLocalToGlobal q).comp S.subtype)
          (Module.Dual.eval (ZMod p) M : Rep.res S.subtype M →ₗ[ZMod p]
            Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p]
            Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) invS θ₀ →
      ∀ (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))),
        IsTheta1 ((primeLocalToGlobal q).comp S.subtype)
          (Module.Dual.eval (ZMod p) M : Rep.res S.subtype M →ₗ[ZMod p]
            Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p]
            Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) invS θ₁ →
      ∀ (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))).ρ.invariants),
        IsTheta2 ((primeLocalToGlobal q).comp S.subtype)
          (Module.Dual.eval (ZMod p) M : Rep.res S.subtype M →ₗ[ZMod p]
            Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p]
            Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) invS θ₂ →
      Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂)
    (θ₀ : M.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH2 (primeLocalToGlobal q) (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hθ₀ : IsTheta0 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) inv θ₀)
    (θ₁ : continuousH1 (primeLocalToGlobal q) M →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH1 (primeLocalToGlobal q) (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hθ₁ : IsTheta1 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) inv θ₁)
    (θ₂ : continuousH2 (primeLocalToGlobal q) M →ₗ[ZMod p] Module.Dual (ZMod p)
      (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ.invariants)
    (hθ₂ : IsTheta2 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) inv θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by
  classical

  let φ : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
      ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)) := Module.Dual.eval (ZMod p) M
  have hφ : Rep.IsEquivariantBilinear M (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) φ :=
    Rep.isEquivariantBilinear_eval_dualTwist M ((cycloChar p).comp (primeLocalToGlobal q))
  let φS : Rep.res S.subtype M →ₗ[ZMod p] Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p]
      Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) := Module.Dual.eval (ZMod p) M
  have hφS : Rep.IsEquivariantBilinear (Rep.res S.subtype M) (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) φS :=
    fun s a b => hφ (s : (primeLocalGaloisGroup q)) a b

  obtain ⟨Fχ, hFχ, hχ1⟩ :=
    groupCohomology.exists_level_ofChar_cycloChar_comp (p := p) (primeLocalToGlobal q) (1 : ZMod p)
  have hsmD : ∀ x : (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))), ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, (primeLocalToGlobal q) s ∈ F.fixingSubgroup → (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ s x = x :=
    Rep.dualTwist_smooth (primeLocalToGlobal q) M ((cycloChar p).comp (primeLocalToGlobal q)) hsm
      ⟨Fχ, hFχ, fun s hs => by
        have h : (((cycloChar p).comp (primeLocalToGlobal q) s : (ZMod p)ˣ) : ZMod p) * 1 = 1 := hχ1 s hs
        rw [mul_one] at h
        exact Units.val_eq_one.mp h⟩
  have hsmDS : ∀ x : Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))), ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))).ρ s x = x := by
    intro x
    obtain ⟨F, hF, h⟩ := hsmD x
    exact ⟨F, hF, fun s hs => h (s : (primeLocalGaloisGroup q)) hs⟩

  obtain ⟨ιN, τN, hιN, hτN, -, hτιN⟩ := Rep.exists_hom_coind_res_comp_eq_index_smul S (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))
  obtain ⟨ιM, τM, hιM, hτM, -, hτιM⟩ := Rep.exists_hom_coind_res_comp_eq_index_smul S M
  obtain ⟨ιD, τD, hιD, hτD, -, hτιD⟩ := Rep.exists_hom_coind_res_comp_eq_index_smul S (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))
  obtain ⟨u, hu⟩ := hSp

  let ShE := LinearEquiv.ofBijective (ShapiroTransport.sh2 S (primeLocalToGlobal q) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) (ShapiroTransport.sh2_bijective S (primeLocalToGlobal q) _ hS)
  let H2τ := continuousH2MapHom (primeLocalToGlobal q) τN
  let H2ι := continuousH2MapHom (primeLocalToGlobal q) ιN
  have H2τι : ∀ y, H2τ (H2ι y) = (u : ZMod p) • y := by
    intro y
    induction y using Submodule.Quotient.induction_on with | _ z =>
    show continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) _ = (u : ZMod p) • continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) z
    rw [← map_smul]
    congr 1
    apply Subtype.ext
    funext st
    show τN.hom (ιN.hom ((z : (primeLocalGaloisGroup q) × (primeLocalGaloisGroup q) → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) ((MonoidHom.id (primeLocalGaloisGroup q)) ((MonoidHom.id (primeLocalGaloisGroup q)) st.1), (MonoidHom.id (primeLocalGaloisGroup q)) ((MonoidHom.id (primeLocalGaloisGroup q)) st.2))))
      = ((u : ZMod p) • (z : (primeLocalGaloisGroup q) × (primeLocalGaloisGroup q) → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) st
    rw [hτιN, hu]
    simp only [MonoidHom.id_apply]
    rfl
  have H2τ_surj : Function.Surjective H2τ := fun y =>
    ⟨H2ι (((u⁻¹ : (ZMod p)ˣ) : ZMod p) • y), by rw [map_smul, map_smul, H2τι, smul_smul, Units.inv_mul, one_smul]⟩

  obtain ⟨hfdS, h1S⟩ := groupCohomology.finrank_continuousH2_ofChar_cycloChar_of_isOpen (p := p) q S hS
  haveI := hfdS
  let invE : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ≃ₗ[ZMod p] ZMod p := LinearEquiv.ofBijective inv hinv
  haveI : FiniteDimensional (ZMod p) (continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) := LinearEquiv.finiteDimensional invE.symm
  haveI : FiniteDimensional (ZMod p) (continuousH2 (primeLocalToGlobal q) (Rep.coind S.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) :=
    LinearEquiv.finiteDimensional ShE.symm
  have hdim : Module.finrank (ZMod p) (continuousH2 (primeLocalToGlobal q) (Rep.coind S.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))))
      = Module.finrank (ZMod p) (continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) := by
    rw [ShE.finrank_eq, h1S, invE.finrank_eq, Module.finrank_self]
  have H2τ_bij : Function.Bijective H2τ :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 H2τ_surj, H2τ_surj⟩
  let H2τE := LinearEquiv.ofBijective H2τ H2τ_bij
  let invS : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p :=
    inv ∘ₗ H2τE.toLinearMap ∘ₗ ShE.symm.toLinearMap
  have hinvS : Function.Bijective invS :=
    hinv.comp (H2τE.bijective.comp ShE.symm.bijective)
  have hinv' : ∀ (w : levelCocycles₂ (primeLocalToGlobal q) (Rep.coind S.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))))
      (w₁ : levelCocycles₂ ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))),
      (∀ s t : S, (w₁ : S × S → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) (s, t)
        = ((w : (primeLocalGaloisGroup q) × (primeLocalGaloisGroup q) → Rep.coind S.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) ((s : (primeLocalGaloisGroup q)), (t : (primeLocalGaloisGroup q))) : (primeLocalGaloisGroup q) → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) 1) →
      inv (continuousH2MapHom (primeLocalToGlobal q) τN (continuousH2π (primeLocalToGlobal q) _ w)) = invS (continuousH2π _ _ w₁) := by
    intro w w₁ hw
    have hSh : ShE (continuousH2π (primeLocalToGlobal q) _ w) = continuousH2π _ _ w₁ := by
      show ShapiroTransport.sh2 S (primeLocalToGlobal q) _ (continuousH2π (primeLocalToGlobal q) _ w) = _
      rw [ShapiroTransport.sh2_π]
      congr 1
      apply Subtype.ext; funext st
      rw [ShapiroTransport.coe_lcU]
      exact (hw st.1 st.2).symm
    show inv (H2τ (continuousH2π (primeLocalToGlobal q) _ w)) = inv (H2τE (ShE.symm (continuousH2π _ _ w₁)))
    rw [← hSh, LinearEquiv.symm_apply_apply]
    rfl

  obtain ⟨⟨θ₀S, hθ₀S⟩, ⟨θ₂S, hθ₂S⟩⟩ := groupCohomology.exists_theta0_and_theta2 ((primeLocalToGlobal q).comp S.subtype) φS hφS invS
  obtain ⟨θ₁S, hθ₁S⟩ := groupCohomology.exists_theta1 ((primeLocalToGlobal q).comp S.subtype) φS hφS hsmDS invS
  have hbijS := hres invS hinvS θ₀S hθ₀S θ₁S hθ₁S θ₂S hθ₂S

  let Ψ : Rep.coind S.subtype (Rep.res S.subtype M) →ₗ[ZMod p] Rep.coind S.subtype (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) :=
    (ShapiroTransport.ptw φS hφS).compr₂ τN.hom.toLinearMap
  have hΨ : ∀ (f : Rep.coind S.subtype (Rep.res S.subtype M)) (g : Rep.coind S.subtype (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))
      (w : Rep.coind S.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))),
      (∀ h : (primeLocalGaloisGroup q), (w : (primeLocalGaloisGroup q) → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) h = φS ((f : (primeLocalGaloisGroup q) → M) h) ((g : (primeLocalGaloisGroup q) → (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))) h)) → Ψ f g = τN.hom w := by
    intro f g w hw
    show τN.hom (ShapiroTransport.ptw φS hφS f g) = τN.hom w
    congr 1
    apply Subtype.ext; funext h
    rw [ShapiroTransport.coe_ptw]
    exact (hw h).symm
  have hΨeq : Rep.IsEquivariantBilinear (Rep.coind S.subtype (Rep.res S.subtype M)) (Rep.coind S.subtype (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))))) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) Ψ := by
    intro g f d
    show τN.hom (ShapiroTransport.ptw φS hφS _ _) = (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))).ρ g (τN.hom (ShapiroTransport.ptw φS hφS f d))
    rw [ShapiroTransport.ptw_equivariant φS hφS g f d, Rep.hom_comm_apply]
  have hsmDS' : ∀ x : Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))), ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, (primeLocalToGlobal q) s ∈ F.fixingSubgroup → (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))).ρ s x = x := hsmDS
  have hsmID : ∀ x : Rep.coind S.subtype (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))), ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧ ∀ g, (primeLocalToGlobal q) g ∈ F.fixingSubgroup → (Rep.coind S.subtype (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))))).ρ g x = x :=
    fun x => Rep.exists_level_coind_apply_eq_self (primeLocalToGlobal q) S hS (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))) hsmDS' x
  obtain ⟨⟨Θ₀, hΘ₀⟩, ⟨Θ₂, hΘ₂⟩⟩ := groupCohomology.exists_theta0_and_theta2 (primeLocalToGlobal q) Ψ hΨeq inv
  obtain ⟨Θ₁, hΘ₁⟩ := groupCohomology.exists_theta1 (primeLocalToGlobal q) Ψ hΨeq hsmID inv
  have hΘbij := groupCohomology.bijective_theta_coind (primeLocalToGlobal q) S hS φS hφS hsmDS invS inv τN hinv' Ψ hΨ
    θ₀S hθ₀S θ₁S hθ₁S θ₂S hθ₂S Θ₀ hΘ₀ Θ₁ hΘ₁ Θ₂ hΘ₂ hbijS

  obtain ⟨hadj1, hadj2⟩ := Rep.coind_pairing_adjoint S φ hφ ιM hιM τM hτM ιD hιD τD hτD τN hτN Ψ hΨ
  let c : ZMod p := ((u⁻¹ : (ZMod p)ˣ) : ZMod p)
  have hcu : c * (S.index : ZMod p) = 1 := by rw [← hu]; exact Units.inv_mul u
  let b : Rep.coind S.subtype (Rep.res S.subtype M) ⟶ M :=
    Rep.ofHom ((c • τM.hom.toLinearMap).intertwiningMap_of_isIntertwiningMap _ M.ρ (fun g x => by
      show c • τM.hom ((Rep.coind S.subtype (Rep.res S.subtype M)).ρ g x) = M.ρ g (c • τM.hom x)
      rw [Rep.hom_comm_apply, map_smul]))
  have hb' : ∀ x, b.hom x = c • τM.hom x := fun _ => rfl
  let b' : (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))) ⟶ Rep.coind S.subtype (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))) :=
    Rep.ofHom ((c • ιD.hom.toLinearMap).intertwiningMap_of_isIntertwiningMap (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ _ (fun g x => by
      show c • ιD.hom ((M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ g x) = (Rep.coind S.subtype (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))))).ρ g (c • ιD.hom x)
      rw [Rep.hom_comm_apply, map_smul]))
  have hb'' : ∀ x, b'.hom x = c • ιD.hom x := fun _ => rfl
  exact groupCohomology.bijective_theta_of_retract (primeLocalToGlobal q) φ Ψ hΨeq ιM b
    (fun m => by rw [hb', hτιM, smul_smul, hcu, one_smul])
    τD b' (fun x => by rw [hb'', map_smul, hτιD, smul_smul, hcu, one_smul])
    (fun m y => hadj1 m y)
    (fun x d => by rw [hb', hb'', map_smul, LinearMap.smul_apply, map_smul, hadj2])
    hsmD inv θ₀ hθ₀ θ₁ hθ₁ θ₂ hθ₂ Θ₀ hΘ₀ Θ₁ hΘ₁ Θ₂ hΘ₂ hΘbij

end S_groupCohomology_bijective_theta_dualTwist_of_res
end P2MW
export P2MW.S_groupCohomology_bijective_theta_dualTwist_of_res (solution)
