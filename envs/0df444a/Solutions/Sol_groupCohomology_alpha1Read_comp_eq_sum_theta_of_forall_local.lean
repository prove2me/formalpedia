-- Prove2me | solution 1 for groupCohomology.alpha1Read_comp_eq_sum_theta_of_forall_local
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/4704f45d-5edc-56e8-a0c9-c696153ded0d

import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Theorems.Thm_groupCohomology_exists_corestriction_map_map_res_eq_map_norm
import Theorems.Thm_groupCohomology_map_delta_eq_delta_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_alpha1Read_comp_eq_sum_theta_of_forall_local

set_option autoImplicit false
set_option maxHeartbeats 6400000
open CategoryTheory groupCohomology ExtCitation

namespace IdSum

universe u

section psi

variable (p : ℕ) [Fact p.Prime]

noncomputable def fInt : ℤ →+ AddCircle (1 : ℚ) where
  toFun k := (((k : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ))
  map_zero' := by simp
  map_add' k k' := by push_cast; rw [add_div, QuotientAddGroup.mk_add]

lemma fInt_p : fInt p (p : ℤ) = 0 := by
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  change (((((p : ℤ) : ℚ)) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) = 0
  rw [Int.cast_natCast, div_self hp]
  exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).2 ⟨1, by simp⟩

noncomputable def psi : ZMod p →+ AddCircle (1 : ℚ) := ZMod.lift p ⟨fInt p, fInt_p p⟩

lemma psi_intCast (k : ℤ) : psi p (k : ZMod p) = (((k : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) :=
  ZMod.lift_coe p ⟨fInt p, fInt_p p⟩ k

lemma psi_apply (n : ZMod p) : psi p n = ((((n.val : ℚ)) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val n]
  rw [← Int.cast_natCast, psi_intCast, Int.cast_natCast]

lemma psi_injective : Function.Injective (psi p) := by
  rw [injective_iff_map_eq_zero]
  intro n hn
  rw [psi_apply, AddCircle.coe_eq_zero_iff] at hn
  obtain ⟨k, hk⟩ := hn
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [zsmul_eq_mul, mul_one, eq_div_iff hp] at hk
  have h2 : (k : ℤ) * p = n.val := by exact_mod_cast hk
  have hdvd : (p : ℤ) ∣ (n.val : ℤ) := Dvd.intro_left k h2
  have : (n.val : ZMod p) = 0 := by
    rw [← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdvd
  rwa [ZMod.natCast_zmod_val] at this

end psi

lemma map_add_hom {k G : Type} [CommRing k] [Group G] {A C : Rep k G} (φ φ' : A ⟶ C) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (φ + φ') n =
      groupCohomology.map (MonoidHom.id G) φ n + groupCohomology.map (MonoidHom.id G) φ' n := by
  have h1 : cochainsMap (MonoidHom.id G) (φ + φ') = cochainsMap (MonoidHom.id G) φ + cochainsMap (MonoidHom.id G) φ' :=
    (cochainsFunctor k G).map_add
  unfold groupCohomology.map
  rw [h1]
  exact (HomologicalComplex.homologyFunctor _ _ n).map_add

noncomputable def evalMap {k G : Type} [CommRing k] [Group G] (A C : Rep k G) (n : ℕ) (z : groupCohomology A n) :
    (A ⟶ C) →+ groupCohomology C n where
  toFun φ := (groupCohomology.map (MonoidHom.id G) φ n).hom z
  map_zero' := by
    rw [show groupCohomology.map (MonoidHom.id G) (0 : A ⟶ C) n = 0 from (groupCohomology.functor k G n).map_zero _ _]
    rfl
  map_add' φ φ' := by
    erw [map_add_hom φ φ' n, ModuleCat.hom_add]
    rfl

lemma evalMap_apply {k G : Type} [CommRing k] [Group G] (A C : Rep k G) (n : ℕ) (z : groupCohomology A n) (φ : A ⟶ C) :
    evalMap A C n z φ = (groupCohomology.map (MonoidHom.id G) φ n).hom z := rfl

lemma nsmul_hom_apply {k G : Type} [CommRing k] [Group G] {A C : Rep k G} (m : ℕ) (f : A ⟶ C) (x : A) :
    (m • f).hom x = m • f.hom x := by
  induction m with
  | zero => rw [zero_nsmul, zero_nsmul]; rfl
  | succ m ih => rw [succ_nsmul, succ_nsmul, Rep.add_hom]; exact congrArg (· + f.hom x) ih

section Counit

variable {k G : Type} [CommRing k] [Group G] (S : Subgroup G)
  [DecidableRel ⇑(QuotientGroup.rightRel S)] [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit [DecidableRel ⇑(QuotientGroup.rightRel S)] [S.FiniteIndex] in

lemma indRes_counit_mk (C : Rep.{0} k G) (h : G) (b : C) :
    ((Rep.indResAdjunction k S.subtype).counit.app C).hom (Representation.IndV.mk S.subtype (Rep.res S.subtype C).ρ h b) =
      C.ρ h⁻¹ b := by
  simp only [Rep.indResAdjunction, Adjunction.mkOfHomEquiv_counit_app]
  change (Rep.Hom.hom ((Rep.indResHomEquiv S.subtype (Rep.res S.subtype C) C).symm (𝟙 _)))
    (Representation.IndV.mk S.subtype (Rep.res S.subtype C).ρ h b) = C.ρ h⁻¹ b
  rw [Rep.indResHomEquiv_symm_apply]
  simp [Representation.IndV.mk, Representation.Coinvariants.lift_mk, TensorProduct.lift.tmul]

lemma coindRes_counit_apply (C : Rep.{0} k G) (f : Rep.coind S.subtype (Rep.res S.subtype C)) :
    ((Rep.coindResAdjunction k S).counit.app C).hom f =
      ∑ q : Quotient (QuotientGroup.rightRel S), q.liftOn (fun g => C.ρ g⁻¹ (f.1 g)) (by
        rintro g₁ g₂ ⟨s, (hs : (s : G) * g₂ = g₁)⟩
        change C.ρ g₁⁻¹ (f.1 g₁) = C.ρ g₂⁻¹ (f.1 g₂)
        have hf : f.1 ((s : G) * g₂) = C.ρ (s : G) (f.1 g₂) := f.2 s g₂
        rw [← hs, hf, mul_inv_rev, map_mul, Module.End.mul_apply, ← Module.End.mul_apply (C.ρ (↑s)⁻¹), ← map_mul,
          inv_mul_cancel, map_one, Module.End.one_apply]) := by
  rw [Rep.coindResAdjunction_counit_app]
  change ((Rep.indResAdjunction k S.subtype).counit.app C).hom (((Rep.res S.subtype C).indCoindIso.inv).hom f) = _
  have hinv : ((Rep.res S.subtype C).indCoindIso.inv).hom f = (Rep.res S.subtype C).coindToInd f := rfl
  rw [hinv, Rep.coindToInd_apply]
  rw [show ∀ y, (Rep.Hom.hom ((Rep.indResAdjunction k S.subtype).counit.app C)) y =
      (Rep.Hom.hom ((Rep.indResAdjunction k S.subtype).counit.app C)).toLinearMap y from fun _ => rfl]
  erw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  induction q using Quotient.inductionOn with
  | h g => exact indRes_counit_mk S C g (f.1 g)

omit [DecidableRel ⇑(QuotientGroup.rightRel S)] [S.FiniteIndex] in

lemma coindMap_unit_apply (R C : Rep.{0} k G) (φ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) (x : R) (g : G) :
    (((Rep.resCoindAdjunction k S.subtype).unit.app R ≫ (Rep.coindFunctor k S.subtype).map φ).hom x).1 g =
      φ.hom (R.ρ g x) := rfl

theorem unit_coindMap_counit_apply [Fintype (G ⧸ S)] (R C : Rep.{0} k G) (φ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) (x : R) :
    ((Rep.resCoindAdjunction k S.subtype).unit.app R ≫ (Rep.coindFunctor k S.subtype).map φ ≫
      (Rep.coindResAdjunction k S).counit.app C).hom x = ∑ g : G ⧸ S, C.ρ g.out (φ.hom (R.ρ g.out⁻¹ x)) := by

  obtain rfl : ‹Fintype (G ⧸ S)› = Subgroup.fintypeQuotientOfFiniteIndex := Subsingleton.elim _ _
  change ((Rep.coindResAdjunction k S).counit.app C).hom
    ((((Rep.resCoindAdjunction k S.subtype).unit.app R ≫ (Rep.coindFunctor k S.subtype).map φ).hom x)) = _
  rw [coindRes_counit_apply]
  apply Fintype.sum_equiv (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
  change C.ρ g⁻¹ ((((Rep.resCoindAdjunction k S.subtype).unit.app R ≫ (Rep.coindFunctor k S.subtype).map φ).hom x).1 g) = _
  rw [coindMap_unit_apply]

  set a : G := ((QuotientGroup.quotientRightRelEquivQuotientLeftRel S) (Quotient.mk _ g)).out with ha_def
  have ha : (QuotientGroup.mk a : G ⧸ S) = QuotientGroup.mk g⁻¹ :=
    Quotient.out_eq ((QuotientGroup.quotientRightRelEquivQuotientLeftRel S) (Quotient.mk _ g))
  rw [QuotientGroup.eq] at ha

  set s : S := ⟨a⁻¹ * g⁻¹, ha⟩ with hs_def
  have ha1 : a⁻¹ = (s : G) * g := by rw [hs_def]; group
  have ha2 : a = g⁻¹ * (s : G)⁻¹ := by rw [← inv_inj, ha1, mul_inv_rev, inv_inv, inv_inv]
  rw [ha1, ha2, map_mul, Module.End.mul_apply]
  have hφ : φ.hom (R.ρ ((s : G) * g) x) = C.ρ (s : G) (φ.hom (R.ρ g x)) := by
    rw [map_mul, Module.End.mul_apply]
    exact Rep.hom_comm_apply φ s (R.ρ g x)
  rw [hφ, ← Module.End.mul_apply (C.ρ (↑s)⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end Counit

lemma norm_id_apply {k G : Type} [CommRing k] [Group G] (S : Subgroup G) [Fintype (G ⧸ S)] (C : Rep k G) (r : C) :
    ((Fintype.card (G ⧸ S) • 𝟙 C : C ⟶ C)).hom r =
      ∑ g : G ⧸ S, C.ρ g.out ((𝟙 (Rep.res S.subtype C) : _).hom (C.ρ g.out⁻¹ r)) := by
  rw [nsmul_hom_apply]
  have h : ∀ g : G ⧸ S, C.ρ g.out ((𝟙 (Rep.res S.subtype C) : _).hom (C.ρ g.out⁻¹ r)) = r := fun g => by
    change C.ρ g.out (C.ρ g.out⁻¹ r) = r
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [Finset.sum_congr rfl fun g _ => h g, Finset.sum_const, Finset.card_univ]
  rfl

end IdSum

open IdSum in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (θ : ∀ v : extArithIndex S,
      continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))
    (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
      locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))

    {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (D : extArithIndex S → Subgroup G) [∀ v, DecidableRel ⇑(QuotientGroup.rightRel (D v))]
    (Yv : ∀ v : extArithIndex S, Rep ℤ ↥(D v)) (C : Rep ℤ G)
    (lam : ∀ v, Yv v ⟶ Rep.res (D v).subtype C)
    (lamJ : GroupCohomology.RepPi.obj (fun v => Rep.coind (D v).subtype (Yv v)) ⟶ C)
    (hlamJ : lamJ = ∑ v, GroupCohomology.RepPi.proj (fun v => Rep.coind (D v).subtype (Yv v)) v ≫
      ((Rep.coindResAdjunction ℤ (D v)).homEquiv (Yv v) C).symm (lam v))

    (B : Rep ℤ G) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (hX : (Rep.relationSeqInt B).ShortExact)
    (hXv : ∀ v, ((Rep.relationSeqInt B).map (Rep.resFunctor (D v).subtype)).ShortExact)

    (invG : ↥(groupCohomology C 2) →+ AddCircle (1 : ℚ))
    (invD : ∀ v, ↥(groupCohomology (Rep.res (D v).subtype C) 2) →+ AddCircle (1 : ℚ))
    (hcor : ∀ (v : extArithIndex S) (cor : ↥(groupCohomology (Rep.res (D v).subtype C) 2) →+ ↥(groupCohomology C 2)),
      (∀ x : ↥(groupCohomology C 2), cor ((groupCohomology.map (D v).subtype (𝟙 (Rep.res (D v).subtype C)) 2).hom x) = (D v).index • x) →
      ∀ y, invG (cor y) = invD v y)

    (al : (Rep.relationModuleInt B ⟶ C) →+ (↥(groupCohomology B 1) →+ ZMod p))
    (hal : ∀ (φ : Rep.relationModuleInt B ⟶ C) (y : ↥(groupCohomology B 1)),
      invG ((groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y)) = ((((al φ y).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)))
    (infl : ↥(groupCohomology B 1) →+ H1 (M.dualTwist (cycloChar p)))
    (Λ : ∀ v, (Rep.res (D v).subtype (Rep.relationModuleInt B) ⟶ Yv v) →+ ↥(continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M)))
    (u : extArithIndex S → (ZMod p)ˣ)

    (hLOC : ∀ (v : extArithIndex S) (sv : Rep.res (D v).subtype (Rep.relationModuleInt B) ⟶ Yv v)
        (x : ↥(groupCohomology B 1)) (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))),
      invD v ((groupCohomology.map (MonoidHom.id ↥(D v)) (sv ≫ lam v) 2).hom
        ((groupCohomology.δ (hXv v) 1 2 rfl).hom
          ((groupCohomology.map (D v).subtype (𝟙 (Rep.res (D v).subtype B)) 1).hom x)))
        = (((((u v : ZMod p) * θ v (Λ v sv) ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)))
    (s : Rep.relationModuleInt B ⟶ GroupCohomology.RepPi.obj (fun v => Rep.coind (D v).subtype (Yv v)))
    (x : ↥(groupCohomology B 1)) (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))) :
    al (s ≫ lamJ) x = ∑ v, (u v : ZMod p) * θ v
      (Λ v (((Rep.resCoindAdjunction ℤ (D v).subtype).homEquiv (Rep.relationModuleInt B) (Yv v)).symm
        (s ≫ GroupCohomology.RepPi.proj (fun v => Rep.coind (D v).subtype (Yv v)) v)))
      ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩ := by
  classical

  haveI : ∀ v, (D v).FiniteIndex := fun v => inferInstance
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  let sv : ∀ v, Rep.res (D v).subtype (Rep.relationModuleInt B) ⟶ Yv v := fun v =>
    ((Rep.resCoindAdjunction ℤ (D v).subtype).homEquiv (Rep.relationModuleInt B) (Yv v)).symm
      (s ≫ GroupCohomology.RepPi.proj (fun v => Rep.coind (D v).subtype (Yv v)) v)
  let φv : ∀ v, Rep.res (D v).subtype (Rep.relationModuleInt B) ⟶ Rep.res (D v).subtype C := fun v => sv v ≫ lam v
  let Nv : ∀ v, Rep.relationModuleInt B ⟶ C := fun v =>
    (s ≫ GroupCohomology.RepPi.proj (fun v => Rep.coind (D v).subtype (Yv v)) v) ≫
      ((Rep.coindResAdjunction ℤ (D v)).homEquiv (Yv v) C).symm (lam v)

  have hNv_eq : ∀ v, Nv v = (Rep.resCoindAdjunction ℤ (D v).subtype).unit.app (Rep.relationModuleInt B) ≫
      (Rep.coindFunctor ℤ (D v).subtype).map (φv v) ≫ (Rep.coindResAdjunction ℤ (D v)).counit.app C := by
    intro v
    have h1 : s ≫ GroupCohomology.RepPi.proj (fun v => Rep.coind (D v).subtype (Yv v)) v =
        ((Rep.resCoindAdjunction ℤ (D v).subtype).homEquiv (Rep.relationModuleInt B) (Yv v)) (sv v) :=
      (Equiv.apply_symm_apply _ _).symm
    change (s ≫ _) ≫ _ = _
    rw [h1, Adjunction.homEquiv_unit, Adjunction.homEquiv_counit]
    erw [Category.assoc, ← (Rep.coindFunctor ℤ (D v).subtype).map_comp_assoc]
  have hNv : ∀ (v) (r : Rep.relationModuleInt B),
      (Nv v).hom r = ∑ g : G ⧸ D v, C.ρ g.out ((φv v).hom ((Rep.relationModuleInt B).ρ g.out⁻¹ r)) := by
    intro v r
    rw [hNv_eq]
    exact IdSum.unit_coindMap_counit_apply (D v) (Rep.relationModuleInt B) C (φv v) r

  have hsum : s ≫ lamJ = ∑ v, Nv v := by
    rw [hlamJ, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    exact (Category.assoc _ _ _).symm

  have hv : ∀ v, invG ((groupCohomology.map (MonoidHom.id G) (Nv v) 2).hom ((groupCohomology.δ hX 1 2 rfl).hom x)) =
      IdSum.psi p ((u v : ZMod p) * θ v (Λ v (sv v)) ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩) := by
    intro v
    obtain ⟨cor, hcor'⟩ := groupCohomology.exists_corestriction_map_map_res_eq_map_norm (D v) C 2

    have hidx : ∀ y : ↥(groupCohomology C 2),
        cor ((groupCohomology.map (D v).subtype (𝟙 (Rep.res (D v).subtype C)) 2).hom y) = (D v).index • y := by
      intro y
      have h := hcor' C (𝟙 _) ((Fintype.card (G ⧸ D v)) • 𝟙 C) (IdSum.norm_id_apply (D v) C) y
      rw [groupCohomology.map_id] at h
      change cor ((groupCohomology.map (D v).subtype (𝟙 (Rep.res (D v).subtype C)) 2).hom y) = _ at h
      rw [h, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
      change IdSum.evalMap C C 2 y (Fintype.card (G ⧸ D v) • 𝟙 C) = _
      rw [map_nsmul, IdSum.evalMap_apply, groupCohomology.map_id]
      rfl

    refine (congrArg invG (hcor' (Rep.relationModuleInt B) (φv v) (Nv v) (hNv v) ((groupCohomology.δ hX 1 2 rfl).hom x)).symm).trans ?_
    rw [hcor v cor hidx]
    have hδ := groupCohomology.map_delta_eq_delta_map (D v).subtype hX (hXv v) (𝟙 _) (𝟙 _) (𝟙 _)
      (by first | (simp; done) | (simp; rfl) | rfl | (ext; simp; rfl)) (by first | (simp; done) | (simp; rfl) | rfl | (ext; simp; rfl)) 1 2 rfl x
    erw [hδ]
    rw [IdSum.psi_apply]
    exact hLOC v (sv v) x hx

  apply IdSum.psi_injective p
  rw [IdSum.psi_apply, ← hal, map_sum, hsum]
  change invG (IdSum.evalMap (Rep.relationModuleInt B) C 2 ((groupCohomology.δ hX 1 2 rfl).hom x) (∑ v, Nv v)) = _
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun v _ => hv v

end S_groupCohomology_alpha1Read_comp_eq_sum_theta_of_forall_local
end P2MW
export P2MW.S_groupCohomology_alpha1Read_comp_eq_sum_theta_of_forall_local (solution)
