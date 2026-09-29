-- Prove2me | solution 1 for groupCohomology.natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/56341d77-5b14-5823-b38a-897661c27b09

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import Theorems.Thm_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image
import Theorems.Thm_groupCohomology_continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
import Theorems.Thm_groupCohomology_natCard_torsionBy_continuousH2_units_eq_of_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory groupCohomology

noncomputable section

local notation "ℚb" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace P2MBrLocA

universe u

variable {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H]
variable {rH : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  {rG : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  (f : G →* H) (hf : ∀ g, rH (f g) = rG g)
  {A : Rep k H} {B : Rep k G} (φ : A →ₗ[k] B) (hφ : ∀ (g : G) (a : A), φ (A.ρ (f g) a) = B.ρ g (φ a))

theorem continuousH2Map_injective_of_surjective_of_bijective (hfs : Function.Surjective f)
    (hφb : Function.Bijective φ) : Function.Injective (continuousH2Map f hf φ hφ) := by
  classical

  set s : H → G := fun h => (hfs h).choose with hs_def
  have hs : ∀ h, f (s h) = h := fun h => (hfs h).choose_spec
  let e : A ≃ₗ[k] B := LinearEquiv.ofBijective φ hφb
  have he : ∀ a, e a = φ a := fun _ => rfl
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    change continuousH2Map f hf φ hφ (continuousH2π rH A c) = 0 at hx
    rw [continuousH2Map_continuousH2π, continuousH2π_eq_zero_iff, coe_levelCocycles₂Map,
      mem_levelCoboundaries₂_iff] at hx
    obtain ⟨w, ⟨F₁, hF₁, hw⟩, hdw⟩ := hx
    change continuousH2π rH A c = 0
    rw [continuousH2π_eq_zero_iff, mem_levelCoboundaries₂_iff]

    refine ⟨fun h => e.symm (w (s h)), ⟨F₁, hF₁, fun h t ht => ?_⟩, ?_⟩
    ·
      change e.symm (w (s (h * t))) = e.symm (w (s h))
      congr 1
      have e1 : s (h * t) = s h * ((s h)⁻¹ * s (h * t)) := by group
      rw [e1]
      apply hw
      rw [← hf, map_mul, map_inv, hs, hs, inv_mul_cancel_left]
      exact ht
    ·
      funext ⟨h₁, h₂⟩
      apply e.injective
      have hκ : w (s (h₁ * h₂)) = w (s h₁ * s h₂) := by
        have e1 : s (h₁ * h₂) = (s h₁ * s h₂) * ((s h₁ * s h₂)⁻¹ * s (h₁ * h₂)) := by group
        rw [e1]
        apply hw
        rw [← hf, map_mul, map_inv, map_mul, map_mul, hs, hs, hs, ← map_mul, inv_mul_cancel, map_one]
        exact one_mem _
      have hd := congrFun hdw (s h₁, s h₂)
      rw [cochainsPullPush₂_apply, hs, hs, d₁₂_hom_apply] at hd
      change e ((A.ρ h₁) (e.symm (w (s h₂))) - e.symm (w (s (h₁ * h₂))) + e.symm (w (s h₁))) =
        e ((c : H × H → A) (h₁, h₂))
      rw [map_add, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, he, he, ← hd, hκ]
      congr 2
      have := hφ (s h₁) (e.symm (w (s h₂)))
      rw [hs] at this
      rw [this, ← he, LinearEquiv.apply_symm_apply]

end P2MBrLocA

namespace P2MBrLocB

local instance isAlgebraicQbar_bl : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_bl : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_bl : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

variable (p : ℕ) [hp : Fact p.Prime] (D : Subgroup Γ)

abbrev Un : Rep ℤ ↥D := Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ ℚb)

abbrev Mu : Rep ℤ ↥D := Rep.res D.subtype (Kummer.kummerRep ℚ ℚb p)

def incl : Mu p D →ₗ[ℤ] Un D := (MonoidHom.toAdditive (rootsOfUnity p ℚb).subtype).toIntLinearMap

lemma incl_apply (a : Mu p D) : incl p D a = Additive.ofMul ((Additive.toMul a : rootsOfUnity p ℚb) : ℚbˣ) := rfl

lemma incl_injective : Function.Injective (incl p D) := fun a b h =>
  Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective h))

lemma incl_equivariant (g : ↥D) (a : Mu p D) : incl p D ((Mu p D).ρ (MonoidHom.id ↥D g) a) = (Un D).ρ g (incl p D a) :=
  rfl

def jD : continuousH2 D.subtype (Mu p D) →ₗ[ℤ] continuousH2 D.subtype (Un D) :=
  continuousH2Map (rH := D.subtype) (rG := D.subtype) (A := Mu p D) (B := Un D) (MonoidHom.id ↥D) (fun _ => rfl)
    (incl p D) (fun _ _ => rfl)

lemma Un_ρ (g : ↥D) (x : Additive ℚbˣ) : (Un D).ρ g x = Additive.ofMul ((g : Γ) • Additive.toMul x) := rfl

def act (g : ↥D) (x : Additive ℚbˣ) : Additive ℚbˣ := Additive.ofMul ((g : Γ) • Additive.toMul x)

lemma act_mul (g h : ↥D) (x : Additive ℚbˣ) : act D (g * h) x = act D g (act D h x) := by
  simp only [act, toMul_ofMul, Subgroup.coe_mul, mul_smul]

def dU₁ (Y : ↥D → Additive ℚbˣ) : ↥D × ↥D → Additive ℚbˣ := (d₁₂ (Un D)).hom Y

lemma dU₁_apply (Y : ↥D → Additive ℚbˣ) (g h : ↥D) : dU₁ D Y (g, h) = act D g (Y h) - Y (g * h) + Y g :=
  d₁₂_hom_apply (Un D) Y (g, h)

lemma dU₁_zsmul (n : ℤ) (Y : ↥D → Additive ℚbˣ) : dU₁ D (n • Y) = n • dU₁ D Y := map_zsmul (d₁₂ (Un D)).hom n Y

lemma dU₁_mem_cocycles₂ (Y : ↥D → Additive ℚbˣ) : dU₁ D Y ∈ cocycles₂ (Un D) := d₁₂_apply_mem_cocycles₂ (A := Un D) Y

lemma exists_normal_level (F' : IntermediateField ℚ ℚb) [FiniteDimensional ℚ F'] :
    ∃ F'' : IntermediateField ℚ ℚb, FiniteDimensional ℚ F'' ∧ (F''.fixingSubgroup.comap D.subtype).Normal ∧
      (F''.fixingSubgroup.comap D.subtype).FiniteIndex ∧ F''.fixingSubgroup ≤ F'.fixingSubgroup := by
  haveI : Normal ℚ (IntermediateField.normalClosure ℚ F' ℚb) := by
    have := normalClosure.normal ℚ (↥F') ℚb; convert this <;> first | rfl | exact Subsingleton.elim _ _
  exact ⟨IntermediateField.normalClosure ℚ F' ℚb, inferInstance, inferInstance, inferInstance,
    IntermediateField.fixingSubgroup_antitone (IntermediateField.le_normalClosure F')⟩

lemma exists_finset_of_isLevelConstant₁ {X : Type} {Y : ↥D → X} (hY : IsLevelConstant₁ D.subtype Y) :
    ∃ (F₀ : IntermediateField ℚ ℚb) (T : Finset ↥D), FiniteDimensional ℚ F₀ ∧
      (F₀.fixingSubgroup.comap D.subtype).Normal ∧
      (∀ g s : ↥D, (s : Γ) ∈ F₀.fixingSubgroup → Y (g * s) = Y g) ∧
      ∀ g : ↥D, ∃ t ∈ T, Y g = Y t := by
  classical
  obtain ⟨F', hF', hc⟩ := hY
  haveI := hF'
  obtain ⟨F₀, hF₀, hN, hFI, hle⟩ := exists_normal_level D F'
  haveI := hFI
  haveI := hN
  let L₀ : Subgroup ↥D := F₀.fixingSubgroup.comap D.subtype
  haveI : Fintype (↥D ⧸ L₀) := Fintype.ofFinite _
  refine ⟨F₀, (Finset.univ : Finset (↥D ⧸ L₀)).image Quotient.out, hF₀, hN, fun g s hs => hc g s (hle hs), fun g => ?_⟩
  refine ⟨(QuotientGroup.mk g : ↥D ⧸ L₀).out, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
  have h : ((QuotientGroup.mk g : ↥D ⧸ L₀).out : ↥D)⁻¹ * g ∈ L₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have : g = (QuotientGroup.mk g : ↥D ⧸ L₀).out * (((QuotientGroup.mk g : ↥D ⧸ L₀).out)⁻¹ * g) := by group
  conv_lhs => rw [this]
  exact hc _ _ (hle h)

lemma exists_pth_root (u : ℚbˣ) : ∃ r : ℚbˣ, r ^ p = u := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : ℚb) hp.out.pos
  have hz0 : z ≠ 0 := by
    intro h; rw [h, zero_pow hp.out.ne_zero] at hz; exact u.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩

def root (x : Additive ℚbˣ) : Additive ℚbˣ := Additive.ofMul (exists_pth_root p (Additive.toMul x)).choose

lemma p_zsmul_root (x : Additive ℚbˣ) : (p : ℤ) • root p x = x := by
  apply Additive.toMul.injective
  rw [toMul_zsmul, zpow_natCast, root, toMul_ofMul, (exists_pth_root p (Additive.toMul x)).choose_spec]

lemma smul_eq_of_mem_fixingSubgroup {u : ℚbˣ} {σ : Γ}
    (hσ : σ ∈ (IntermediateField.adjoin ℚ {((u : ℚbˣ) : ℚb)}).fixingSubgroup) : σ • u = u := by
  ext
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (IntermediateField.mem_adjoin_simple_self ℚ _)

private lemma _root_.P2MBrLocB.finiteDimensional_adjoin (a : ℚb) : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {a}) := by
  have := IntermediateField.adjoin.finiteDimensional ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).isIntegral)
  convert this

p2m_export "P2MBrLocB" "finiteDimensional_adjoin"
lemma finiteDimensional_sup' {E E' : IntermediateField ℚ ℚb} (h : FiniteDimensional ℚ E) (h' : FiniteDimensional ℚ E') :
    FiniteDimensional ℚ (↥(E ⊔ E')) := by
  have := @IntermediateField.finiteDimensional_sup ℚ ℚb _ _ _ E E' (by convert h) (by convert h')
  convert this

lemma finiteDimensional_finset_sup {ι : Type} (T : Finset ι) (E : ι → IntermediateField ℚ ℚb)
    (h : ∀ i, FiniteDimensional ℚ (E i)) : FiniteDimensional ℚ (↥(T.sup E)) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sup_empty]; exact (inferInstance : FiniteDimensional ℚ (⊥ : IntermediateField ℚ ℚb))
  | insert a T ha ih => rw [Finset.sup_insert]; exact finiteDimensional_sup' (h a) ih

lemma exists_level_root {Y : ↥D → Additive ℚbˣ} (hY : IsLevelConstant₁ D.subtype Y) :
    ∃ F₂ : IntermediateField ℚ ℚb, FiniteDimensional ℚ F₂ ∧ (F₂.fixingSubgroup.comap D.subtype).Normal ∧
      (∀ g s : ↥D, (s : Γ) ∈ F₂.fixingSubgroup → root p (Y (g * s)) = root p (Y g)) ∧
      (∀ g s : ↥D, (s : Γ) ∈ F₂.fixingSubgroup → act D s (root p (Y g)) = root p (Y g)) := by
  classical
  obtain ⟨F₀, T, hF₀, hN, hcY, hT⟩ := exists_finset_of_isLevelConstant₁ D hY
  haveI := hF₀
  let F₁ : IntermediateField ℚ ℚb :=
    F₀ ⊔ T.sup fun t => IntermediateField.adjoin ℚ {((Additive.toMul (root p (Y t)) : ℚbˣ) : ℚb)}
  haveI hF₁ : FiniteDimensional ℚ F₁ :=
    finiteDimensional_sup' hF₀ (finiteDimensional_finset_sup _ _ fun _ => finiteDimensional_adjoin _)
  have hF₁₀ : F₁.fixingSubgroup ≤ F₀.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left
  obtain ⟨F₂, hF₂, hN₂, -, hle₂⟩ := exists_normal_level D F₁
  refine ⟨F₂, hF₂, hN₂, fun g s hs => by rw [hcY g s (hF₁₀ (hle₂ hs))], fun g s hs => ?_⟩
  obtain ⟨t, ht, hgt⟩ := hT g
  rw [hgt, act]
  congr 1
  apply smul_eq_of_mem_fixingSubgroup
  refine IntermediateField.fixingSubgroup_antitone ?_ (hle₂ hs)
  exact le_sup_of_le_right
    (Finset.le_sup (f := fun t => IntermediateField.adjoin ℚ {((Additive.toMul (root p (Y t)) : ℚbˣ) : ℚb)}) ht)

lemma isLevelConstant₂_dU₁ {Y₁ : ↥D → Additive ℚbˣ} {F₂ : IntermediateField ℚ ℚb} (hF₂ : FiniteDimensional ℚ F₂)
    (hN₂ : (F₂.fixingSubgroup.comap D.subtype).Normal)
    (hc : ∀ g s : ↥D, (s : Γ) ∈ F₂.fixingSubgroup → Y₁ (g * s) = Y₁ g)
    (hv : ∀ g s : ↥D, (s : Γ) ∈ F₂.fixingSubgroup → act D s (Y₁ g) = Y₁ g) :
    IsLevelConstant₂ D.subtype (dU₁ D Y₁) := by
  refine ⟨F₂, hF₂, fun g g' s s' hs hs' => ?_⟩
  rw [dU₁_apply, dU₁_apply]
  have e1 : g * s * (g' * s') = g * g' * (g'⁻¹ * s * g' * s') := by group
  have hs2 : (((g'⁻¹ * s * g' * s') : ↥D) : Γ) ∈ F₂.fixingSubgroup := by
    have h1 : g'⁻¹ * s * g' ∈ F₂.fixingSubgroup.comap D.subtype := hN₂.conj_mem' s hs g'
    exact (F₂.fixingSubgroup.comap D.subtype).mul_mem h1 hs'
  rw [e1, hc _ _ hs2, hc _ _ hs, hc _ _ hs', act_mul, hv _ _ hs]

def toMu {x : Additive ℚbˣ} (hx : (p : ℤ) • x = 0) : Additive (rootsOfUnity p ℚb) :=
  Additive.ofMul ⟨Additive.toMul x, by
    rw [mem_rootsOfUnity]
    have := congrArg Additive.toMul hx
    rwa [toMul_zsmul, zpow_natCast, toMul_zero] at this⟩

lemma incl_toMu {x : Additive ℚbˣ} (hx : (p : ℤ) • x = 0) : incl p D (toMu p hx) = x := rfl

def inclF (a : Additive (rootsOfUnity p ℚb)) : Additive ℚbˣ := Additive.ofMul ((Additive.toMul a : rootsOfUnity p ℚb) : ℚbˣ)

lemma incl_eq_inclF (a : Mu p D) : incl p D a = inclF p a := rfl

lemma inclF_injective : Function.Injective (inclF p) := fun a b h =>
  Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective h))

lemma p_zsmul_mu (a : Additive (rootsOfUnity p ℚb)) : (p : ℤ) • a = 0 := by
  apply Additive.toMul.injective
  rw [toMul_zsmul, zpow_natCast, toMul_zero]
  exact Subtype.ext ((mem_rootsOfUnity _ _).1 (Additive.toMul a).2)

theorem exists_levelCocycles₂_incl_sub_mem (X : ↥D × ↥D → Additive ℚbˣ) (hX : X ∈ levelCocycles₂ D.subtype (Un D))
    (hpX : (p : ℤ) • X ∈ levelCoboundaries₂ D.subtype (Un D)) :
    ∃ z : ↥D × ↥D → Additive (rootsOfUnity p ℚb), z ∈ levelCocycles₂ D.subtype (Mu p D) ∧
      X - (inclF p) ∘ z ∈ levelCoboundaries₂ D.subtype (Un D) := by
  classical
  obtain ⟨Y, hY, hYX⟩ := (mem_levelCoboundaries₂_iff _ _ _).1 hpX
  change ↥D → Additive ℚbˣ at Y
  change dU₁ D Y = (p : ℤ) • X at hYX

  obtain ⟨Y₁, hY₁⟩ : ∃ Y₁ : ↥D → Additive ℚbˣ, Y₁ = fun g => root p (Y g) := ⟨_, rfl⟩
  have hY₁p : (p : ℤ) • Y₁ = Y := by subst hY₁; exact funext fun g => p_zsmul_root p (Y g)
  obtain ⟨F₂, hF₂, hN₂, hc₀, hv₀⟩ := exists_level_root p D hY
  have hc : ∀ g s : ↥D, (s : Γ) ∈ F₂.fixingSubgroup → Y₁ (g * s) = Y₁ g := by subst hY₁; exact hc₀
  have hv : ∀ g s : ↥D, (s : Γ) ∈ F₂.fixingSubgroup → act D s (Y₁ g) = Y₁ g := by subst hY₁; exact hv₀
  have hY₁l : IsLevelConstant₁ D.subtype Y₁ := ⟨F₂, hF₂, hc⟩
  have hdY₁ : IsLevelConstant₂ D.subtype (dU₁ D Y₁) := isLevelConstant₂_dU₁ D hF₂ hN₂ hc hv

  obtain ⟨hXc, hXl⟩ := (mem_levelCocycles₂_iff _ _ _).1 hX
  obtain ⟨X', hX'⟩ : ∃ X' : ↥D × ↥D → Additive ℚbˣ, X' = X - dU₁ D Y₁ := ⟨_, rfl⟩
  have hX'c : X' ∈ cocycles₂ (Un D) := by rw [hX']; exact Submodule.sub_mem _ hXc (dU₁_mem_cocycles₂ D Y₁)
  have hX'l : IsLevelConstant₂ D.subtype X' := by
    have := hXl.add (hdY₁.comp (fun v => -v))
    rw [hX', sub_eq_add_neg]
    exact this
  have hX'p : ∀ g, (p : ℤ) • X' g = 0 := by
    intro g
    have e1 : ((p : ℤ) • X) g = dU₁ D Y g := (congrFun hYX g).symm
    have e2 : dU₁ D Y g = (p : ℤ) • dU₁ D Y₁ g := by rw [← hY₁p, dU₁_zsmul]; rfl
    rw [hX', Pi.sub_apply, zsmul_sub, ← e2, ← e1, Pi.smul_apply, sub_self]

  let z : ↥D × ↥D → Additive (rootsOfUnity p ℚb) := fun g => toMu p (hX'p g)
  have hzX : (inclF p) ∘ z = X' := funext fun g => incl_toMu p D (hX'p g)
  refine ⟨z, (mem_levelCocycles₂_iff _ _ _).2 ⟨?_, ?_⟩, ?_⟩
  · rw [mem_cocycles₂_iff]
    intro g h j
    apply incl_injective p D
    rw [map_add, map_add]
    have := (mem_cocycles₂_iff (A := Un D) X').1 hX'c g h j
    rw [← hzX] at this
    exact this
  · obtain ⟨F, hF, hcst⟩ := hX'l
    refine ⟨F, hF, fun g g' s s' hs hs' => inclF_injective p ?_⟩
    have := hcst g g' s s' hs hs'
    rw [← hzX] at this
    exact this
  · rw [hzX, hX', sub_sub_cancel]
    exact (mem_levelCoboundaries₂_iff _ _ _).2 ⟨Y₁, hY₁l, rfl⟩

theorem exists_jD_eq (x : continuousH2 D.subtype (Un D)) (hx : (p : ℤ) • x = 0) :
    ∃ u : continuousH2 D.subtype (Mu p D), jD p D u = x := by
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    have hpX : (p : ℤ) • (c : ↥D × ↥D → Un D) ∈ levelCoboundaries₂ D.subtype (Un D) := by
      have : continuousH2π D.subtype (Un D) ((p : ℤ) • c) = 0 := by rw [map_zsmul]; exact hx
      exact (continuousH2π_eq_zero_iff _ _ _).1 this
    obtain ⟨z, hz, hsub⟩ := exists_levelCocycles₂_incl_sub_mem p D c.1 c.2 hpX
    refine ⟨continuousH2π D.subtype (Mu p D) ⟨z, hz⟩, ?_⟩
    change continuousH2Map _ _ _ _ (continuousH2π D.subtype (Mu p D) ⟨z, hz⟩) = continuousH2π D.subtype (Un D) c
    rw [continuousH2Map_continuousH2π, ← sub_eq_zero, ← map_sub, continuousH2π_eq_zero_iff]
    have : ((levelCocycles₂Map (rH := D.subtype) (rG := D.subtype) (A := Mu p D) (B := Un D) (MonoidHom.id ↥D)
        (fun _ => rfl) (incl p D) (fun _ _ => rfl) ⟨z, hz⟩ - c : ↥(levelCocycles₂ D.subtype (Un D))) :
        ↥D × ↥D → Un D) = -((show ↥D × ↥D → Additive ℚbˣ from c.1) - inclF p ∘ z) := by
      rw [Submodule.coe_sub, coe_levelCocycles₂Map, neg_sub]
      rfl
    rw [this]
    exact Submodule.neg_mem _ hsub

theorem p_smul_eq_zero (u : continuousH2 D.subtype (Mu p D)) : (p : ℤ) • u = 0 := by
  induction u using Submodule.Quotient.induction_on with
  | H c =>
    have : (p : ℤ) • c = 0 := by
      apply Subtype.ext
      funext g
      change (p : ℤ) • ((c : ↥D × ↥D → Mu p D) g) = 0
      exact p_zsmul_mu p _
    change continuousH2π D.subtype (Mu p D) ((p : ℤ) • c) = 0
    rw [this, map_zero]

end P2MBrLocB

namespace P2MBrLocC

variable (q : ℕ) [Fact q.Prime] (p : ℕ) [hp : Fact p.Prime]
variable (F : IntermediateField ℚ ℚb) [FiniteDimensional ℚ F] (g : Γ)

local notation "Ω" => PadicAlgCl q
local notation "ι" => padicEmbedding q
local notation "rq" => localGaloisToGlobal q

abbrev mapLevel (e : Γ) (E : IntermediateField ℚ ℚb) : IntermediateField ℚ ℚb := E.map (e : ℚb →ₐ[ℚ] ℚb)

lemma mem_fixingSubgroup_mapLevel_iff (e γ : Γ) (E : IntermediateField ℚ ℚb) :
    γ ∈ (mapLevel e E).fixingSubgroup ↔ e⁻¹ * γ * e ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := h (e x) ⟨x, hx, rfl⟩
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    change e.symm (γ (e x)) = x
    rw [this, AlgEquiv.symm_apply_apply]
  · rintro h _ ⟨x, hx, rfl⟩
    have := h x hx
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
    change e.symm (γ (e x)) = x at this
    change γ (e x) = e x
    rw [← e.apply_symm_apply (γ (e x)), this]

lemma mem_fixingSubgroup_adjoin_iff {K L : Type*} [Field K] [Field L] [Algebra K L] (S : Set L) (τ : L ≃ₐ[K] L) :
    τ ∈ (IntermediateField.adjoin K S).fixingSubgroup ↔ ∀ y ∈ S, τ y = y := by
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
  constructor
  · intro h y hy
    exact (IntermediateField.mem_fixedField_iff _ _).1 (h hy) τ (Subgroup.mem_zpowers τ)
  · intro h y hy
    change y ∈ IntermediateField.fixedField (Subgroup.zpowers τ)
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have : Subgroup.zpowers τ ≤ MulAction.stabilizer (L ≃ₐ[K] L) y := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]; exact h y hy
    exact this hf

abbrev F' : IntermediateField ℚ ℚb := mapLevel g⁻¹ F

abbrev K' : IntermediateField ℚ_[q] Ω := IntermediateField.adjoin ℚ_[q] (ι '' ((F' F g : IntermediateField ℚ ℚb) : Set ℚb))

scoped instance finiteDimensional_K' : FiniteDimensional ℚ_[q] (K' q F g) :=
  IntermediateField.finiteDimensional_adjoin_padicEmbedding_image q (F' F g)

def resK : (Ω ≃ₐ[K' q F g] Ω) →* (Ω ≃ₐ[ℚ_[q]] Ω) := MonoidHom.mk' (fun σ => σ.restrictScalars ℚ_[q]) (fun _ _ => rfl)

lemma resK_apply (σ : Ω ≃ₐ[K' q F g] Ω) (x : Ω) : resK q F g σ x = σ x := rfl

lemma resK_mem_fixingSubgroup (σ : Ω ≃ₐ[K' q F g] Ω) : resK q F g σ ∈ (K' q F g).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact σ.commutes ⟨x, hx⟩

lemma resK_fixingSubgroupEquiv (τ : (K' q F g).fixingSubgroup) :
    resK q F g (IntermediateField.fixingSubgroupEquiv (K' q F g) τ) = τ := AlgEquiv.ext fun _ => rfl

def r' : (Ω ≃ₐ[K' q F g] Ω) →* Γ := ((MulAut.conj g).toMonoidHom.comp rq).comp (resK q F g)

lemma r'_apply (σ : Ω ≃ₐ[K' q F g] Ω) : r' q F g σ = g * rq (resK q F g σ) * g⁻¹ := rfl

abbrev D : Subgroup Γ := F.fixingSubgroup ⊓ ((rq).range.map (MulAut.conj g).toMonoidHom)

lemma rq_mem_fixingSubgroup_F'_iff (τ : Ω ≃ₐ[ℚ_[q]] Ω) :
    rq τ ∈ (F' F g).fixingSubgroup ↔ τ ∈ (K' q F g).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, mem_fixingSubgroup_adjoin_iff]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    rw [← padicEmbedding_localGaloisToGlobal, h x hx]
  · intro h x hx
    apply (padicEmbedding q).toRingHom.injective
    change ι (rq τ x) = ι x
    rw [padicEmbedding_localGaloisToGlobal]
    exact h _ ⟨x, hx, rfl⟩

lemma conj_mem_fixingSubgroup_iff (E : IntermediateField ℚ ℚb) (γ' : Γ) :
    g * γ' * g⁻¹ ∈ E.fixingSubgroup ↔ γ' ∈ (mapLevel g⁻¹ E).fixingSubgroup := by
  rw [mem_fixingSubgroup_mapLevel_iff, inv_inv]

lemma r'_mem_D (σ : Ω ≃ₐ[K' q F g] Ω) : r' q F g σ ∈ D q F g := by
  refine Subgroup.mem_inf.2 ⟨?_, ⟨rq (resK q F g σ), ⟨_, rfl⟩, rfl⟩⟩
  rw [r'_apply, conj_mem_fixingSubgroup_iff, rq_mem_fixingSubgroup_F'_iff]
  exact resK_mem_fixingSubgroup q F g σ

def π : (Ω ≃ₐ[K' q F g] Ω) →* ↥(D q F g) := (r' q F g).codRestrict (D q F g) (r'_mem_D q F g)

lemma subtype_π (σ : Ω ≃ₐ[K' q F g] Ω) : (D q F g).subtype (π q F g σ) = r' q F g σ := rfl

lemma π_surjective : Function.Surjective (π q F g) := by
  rintro ⟨γ, hγF, ⟨_, ⟨τ, rfl⟩, hγ⟩⟩
  change g * rq τ * g⁻¹ = γ at hγ
  have hτ : τ ∈ (K' q F g).fixingSubgroup := by
    rw [← rq_mem_fixingSubgroup_F'_iff, ← conj_mem_fixingSubgroup_iff, hγ]; exact hγF
  refine ⟨IntermediateField.fixingSubgroupEquiv (K' q F g) ⟨τ, hτ⟩, Subtype.ext ?_⟩
  change r' q F g _ = γ
  rw [r'_apply, resK_fixingSubgroupEquiv, ← hγ]

lemma hopen' (F₁ : IntermediateField ℚ ℚb) (hF₁ : FiniteDimensional ℚ F₁) :
    ∃ E : IntermediateField (K' q F g) Ω, FiniteDimensional (K' q F g) E ∧
      ∀ σ : Ω ≃ₐ[K' q F g] Ω, σ ∈ E.fixingSubgroup → r' q F g σ ∈ F₁.fixingSubgroup := by
  classical
  haveI := hF₁

  have h := (exists_finiteDimensional_comap_localGaloisToGlobal_iff q
    (fun U => U ≤ (mapLevel g⁻¹ F₁).fixingSubgroup.comap rq) (fun U V hVU hU => hVU.trans hU)).1
    ⟨mapLevel g⁻¹ F₁, inferInstance, le_rfl⟩
  obtain ⟨K₁, hK₁, hle⟩ := h
  haveI := hK₁

  let b := Module.finBasis ℚ_[q] K₁
  let S : Set Ω := Set.range fun i => ((b i : K₁) : Ω)
  refine ⟨IntermediateField.adjoin (K' q F g) S, ?_, fun σ hσ => ?_⟩
  · apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    exact (Algebra.IsAlgebraic.isAlgebraic (R := K' q F g) x).isIntegral
  · rw [r'_apply, conj_mem_fixingSubgroup_iff]
    have hσ' : ∀ i, σ ((b i : K₁) : Ω) = ((b i : K₁) : Ω) := fun i =>
      (mem_fixingSubgroup_adjoin_iff S σ).1 hσ _ ⟨i, rfl⟩
    have hmem : resK q F g σ ∈ K₁.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hx' : (⟨x, hx⟩ : K₁) = ∑ i, b.repr ⟨x, hx⟩ i • b i := (b.sum_repr ⟨x, hx⟩).symm
      have hx'' : x = ∑ i, algebraMap ℚ_[q] Ω (b.repr ⟨x, hx⟩ i) * ((b i : K₁) : Ω) := by
        have := congrArg Subtype.val hx'
        rw [IntermediateField.coe_sum] at this
        refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
        rw [IntermediateField.coe_smul, Algebra.smul_def]
      rw [hx'', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, AlgEquiv.commutes, resK_apply, hσ' i]
    exact hle hmem

lemma hlevel' (E : IntermediateField (K' q F g) Ω) (hE : FiniteDimensional (K' q F g) E) :
    ∃ F₁ : IntermediateField ℚ ℚb, FiniteDimensional ℚ F₁ ∧
      ∀ σ : Ω ≃ₐ[K' q F g] Ω, r' q F g σ ∈ F₁.fixingSubgroup → σ ∈ E.fixingSubgroup := by
  classical
  haveI := hE
  haveI : Module.Free (K' q F g) E := Module.Free.of_divisionRing (K' q F g) E

  let bK := Module.finBasis ℚ_[q] (K' q F g)
  let bE := Module.finBasis (K' q F g) E
  let S : Set Ω := (Set.range fun i => ((bK i : K' q F g) : Ω)) ∪ Set.range fun j => ((bE j : E) : Ω)
  let K₁ : IntermediateField ℚ_[q] Ω := IntermediateField.adjoin ℚ_[q] S
  haveI hK₁ : FiniteDimensional ℚ_[q] K₁ := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[q]) x).isIntegral

  have hfix : ∀ τ : Ω ≃ₐ[ℚ_[q]] Ω, τ ∈ K₁.fixingSubgroup → ∀ x : Ω, x ∈ E → τ x = x := by
    intro τ hτ x hx
    rw [mem_fixingSubgroup_adjoin_iff] at hτ
    have hK : ∀ i, τ ((bK i : K' q F g) : Ω) = ((bK i : K' q F g) : Ω) := fun i => hτ _ (Or.inl ⟨i, rfl⟩)
    have hEb : ∀ j, τ ((bE j : E) : Ω) = ((bE j : E) : Ω) := fun j => hτ _ (Or.inr ⟨j, rfl⟩)

    have hK'fix : ∀ c : K' q F g, τ (c : Ω) = c := by
      intro c
      have hc : c = ∑ i, bK.repr c i • bK i := (bK.sum_repr c).symm
      have hc' : (c : Ω) = ∑ i, algebraMap ℚ_[q] Ω (bK.repr c i) * ((bK i : K' q F g) : Ω) := by
        have := congrArg Subtype.val hc
        rw [IntermediateField.coe_sum] at this
        refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
        rw [IntermediateField.coe_smul, Algebra.smul_def]
      rw [hc', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, AlgEquiv.commutes, hK i]
    have hx' : (⟨x, hx⟩ : E) = ∑ j, bE.repr ⟨x, hx⟩ j • bE j := (bE.sum_repr ⟨x, hx⟩).symm
    have hx'' : x = ∑ j, ((bE.repr ⟨x, hx⟩ j : K' q F g) : Ω) * ((bE j : E) : Ω) := by
      have := congrArg Subtype.val hx'
      rw [IntermediateField.coe_sum] at this
      refine this.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [IntermediateField.coe_smul, Algebra.smul_def]; rfl
    rw [hx'', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hK'fix, hEb j]

  have h := (exists_finiteDimensional_comap_localGaloisToGlobal_iff q
    (fun U => ∀ τ ∈ U, ∀ x : Ω, x ∈ E → τ x = x) (fun U V hVU hU τ hτ => hU τ (hVU hτ))).2
    ⟨K₁, hK₁, hfix⟩
  obtain ⟨F₂, hF₂, hF₂fix⟩ := h
  haveI := hF₂
  refine ⟨mapLevel g F₂, inferInstance, fun σ hσ => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hmem : resK q F g σ ∈ F₂.fixingSubgroup.comap rq := by
    rw [Subgroup.mem_comap]
    rw [r'_apply, mem_fixingSubgroup_mapLevel_iff, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
      mul_assoc, inv_mul_cancel, mul_one] at hσ
    exact hσ
  exact hF₂fix _ hmem x hx

def θ : ℚb →+* Ω := (padicEmbedding q).toRingHom.comp ((g⁻¹ : Γ) : ℚb →+* ℚb)

lemma θ_apply (x : ℚb) : θ q g x = ι (g⁻¹ x) := rfl

lemma θ_injective : Function.Injective (θ q g) := (θ q g).injective

lemma θ_r' (σ : Ω ≃ₐ[K' q F g] Ω) (x : ℚb) : θ q g (r' q F g σ x) = σ (θ q g x) := by
  rw [θ_apply, θ_apply, r'_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
  rw [← AlgEquiv.mul_apply g⁻¹ g, inv_mul_cancel, AlgEquiv.one_apply, padicEmbedding_localGaloisToGlobal]
  rfl

abbrev UnD : Rep ℤ ↥(D q F g) := Rep.res (D q F g).subtype (Rep.ofAlgebraAutOnUnits ℚ ℚb)
abbrev MuD : Rep ℤ ↥(D q F g) := Rep.res (D q F g).subtype (Kummer.kummerRep ℚ ℚb p)
abbrev UnΩ : Rep ℤ (Ω ≃ₐ[K' q F g] Ω) := Rep.ofAlgebraAutOnUnits (K' q F g) Ω
abbrev MuΩ : Rep ℤ (Ω ≃ₐ[K' q F g] Ω) := Kummer.kummerRep (K' q F g) Ω p

def φU : UnD q F g →ₗ[ℤ] UnΩ q F g := (MonoidHom.toAdditive (Units.map (θ q g).toMonoidHom)).toIntLinearMap

def φμ : MuD q p F g →ₗ[ℤ] MuΩ q p F g := (MonoidHom.toAdditive (restrictRootsOfUnity (θ q g) p)).toIntLinearMap

lemma φU_apply (a : UnD q F g) :
    φU q F g a = Additive.ofMul (Units.map (θ q g).toMonoidHom (Additive.toMul a)) := rfl

lemma φμ_apply (a : MuD q p F g) :
    φμ q p F g a = Additive.ofMul (restrictRootsOfUnity (θ q g) p (Additive.toMul a)) := rfl

lemma φU_equivariant (σ : Ω ≃ₐ[K' q F g] Ω) (a : UnD q F g) :
    φU q F g ((UnD q F g).ρ (π q F g σ) a) = (UnΩ q F g).ρ σ (φU q F g a) := by
  apply Additive.toMul.injective
  apply Units.ext
  change θ q g ((r' q F g σ) (Additive.toMul a : ℚbˣ)) = σ (θ q g (Additive.toMul a : ℚbˣ))
  exact θ_r' q F g σ _

lemma φμ_equivariant (σ : Ω ≃ₐ[K' q F g] Ω) (a : MuD q p F g) :
    φμ q p F g ((MuD q p F g).ρ (π q F g σ) a) = (MuΩ q p F g).ρ σ (φμ q p F g a) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change θ q g ((r' q F g σ) ((Additive.toMul a : rootsOfUnity p ℚb) : ℚbˣ)) =
    σ (θ q g ((Additive.toMul a : rootsOfUnity p ℚb) : ℚbˣ))
  exact θ_r' q F g σ _

lemma φμ_injective : Function.Injective (φμ q p F g) := by
  intro a b h
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply θ_injective q g
  have := congrArg (fun x : MuΩ q p F g => (((Additive.toMul x : rootsOfUnity p Ω) : Ωˣ) : Ω)) h
  exact this

lemma φμ_bijective : Function.Bijective (φμ q p F g) := by
  classical
  haveI : NeZero (p : ℚb) := NeZero.charZero
  haveI : NeZero (p : Ω) := NeZero.charZero
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hc1 : Nat.card (MuD q p F g) = p := HasEnoughRootsOfUnity.natCard_rootsOfUnity ℚb p
  have hc2 : Nat.card (MuΩ q p F g) = p := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω p
  haveI : Finite (MuΩ q p F g) := Nat.finite_of_card_ne_zero (by rw [hc2]; exact hp.out.ne_zero)
  haveI : Finite (MuD q p F g) := Nat.finite_of_card_ne_zero (by rw [hc1]; exact hp.out.ne_zero)
  exact (Nat.bijective_iff_injective_and_card _).2 ⟨φμ_injective q p F g, by rw [hc1, hc2]⟩

def Ψ : continuousH2 (D q F g).subtype (MuD q p F g) →ₗ[ℤ] continuousH2 (r' q F g) (MuΩ q p F g) :=
  continuousH2Map (rH := (D q F g).subtype) (rG := r' q F g) (A := MuD q p F g) (B := MuΩ q p F g)
    (π q F g) (subtype_π q F g) (φμ q p F g) (φμ_equivariant q p F g)

def jΩ : continuousH2 (r' q F g) (MuΩ q p F g) →ₗ[ℤ] continuousH2 (r' q F g) (UnΩ q F g) :=
  continuousH2Map (rH := r' q F g) (rG := r' q F g) (A := MuΩ q p F g) (B := UnΩ q F g)
    (MonoidHom.id _) (fun _ => rfl) (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap (fun _ _ => rfl)

lemma jΩ_injective_and_range :
    Function.Injective (jΩ q p F g) ∧
      (∀ x : continuousH2 (r' q F g) (UnΩ q F g), x ∈ LinearMap.range (jΩ q p F g) ↔ (p : ℤ) • x = 0) :=
  groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero p (r' q F g)
    (hlevel' q F g) (hopen' q F g)

lemma natCard_torsionBy_Ω : Nat.card ↥(Submodule.torsionBy ℤ (continuousH2 (r' q F g) (UnΩ q F g)) (p : ℤ)) = p :=
  groupCohomology.natCard_torsionBy_continuousH2_units_eq_of_padic q (K' q F g) (r' q F g) (hlevel' q F g) (hopen' q F g) p

theorem main :
    Finite ↥(Submodule.torsionBy ℤ (continuousH2 (D q F g).subtype (UnD q F g)) (p : ℤ)) ∧
    Nat.card ↥(Submodule.torsionBy ℤ (continuousH2 (D q F g).subtype (UnD q F g)) (p : ℤ)) ≤ p := by

  have hY : Nat.card ↥(Submodule.torsionBy ℤ (continuousH2 (r' q F g) (UnΩ q F g)) (p : ℤ)) = p :=
    natCard_torsionBy_Ω q p F g
  haveI : Finite ↥(Submodule.torsionBy ℤ (continuousH2 (r' q F g) (UnΩ q F g)) (p : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hY]; exact hp.out.ne_zero)
  obtain ⟨hjinj, hjrange⟩ := jΩ_injective_and_range q p F g

  let e₁ : continuousH2 (r' q F g) (MuΩ q p F g) →
      ↥(Submodule.torsionBy ℤ (continuousH2 (r' q F g) (UnΩ q F g)) (p : ℤ)) :=
    fun v => ⟨jΩ q p F g v, (Submodule.mem_torsionBy_iff _ _).2 ((hjrange _).1 ⟨v, rfl⟩)⟩
  have he₁ : Function.Injective e₁ := fun a b h => hjinj (congrArg Subtype.val h)
  haveI : Finite (continuousH2 (r' q F g) (MuΩ q p F g)) := Finite.of_injective e₁ he₁

  have hΨ : Function.Injective (Ψ q p F g) :=
    P2MBrLocA.continuousH2Map_injective_of_surjective_of_bijective _ _ _ _ (π_surjective q F g) (φμ_bijective q p F g)
  haveI : Finite (continuousH2 (D q F g).subtype (MuD q p F g)) := Finite.of_injective _ hΨ

  let e₃ : continuousH2 (D q F g).subtype (MuD q p F g) →
      ↥(Submodule.torsionBy ℤ (continuousH2 (D q F g).subtype (UnD q F g)) (p : ℤ)) :=
    fun u => ⟨P2MBrLocB.jD p (D q F g) u, (Submodule.mem_torsionBy_iff _ _).2
      (by rw [← map_zsmul, P2MBrLocB.p_smul_eq_zero, map_zero])⟩
  have he₃ : Function.Surjective e₃ := by
    rintro ⟨x, hx⟩
    obtain ⟨u, hu⟩ := P2MBrLocB.exists_jD_eq p (D q F g) x ((Submodule.mem_torsionBy_iff _ _).1 hx)
    exact ⟨u, Subtype.ext hu⟩
  refine ⟨Finite.of_surjective e₃ he₃, ?_⟩
  calc Nat.card ↥(Submodule.torsionBy ℤ (continuousH2 (D q F g).subtype (UnD q F g)) (p : ℤ))
      ≤ Nat.card (continuousH2 (D q F g).subtype (MuD q p F g)) := Nat.card_le_card_of_surjective e₃ he₃
    _ ≤ Nat.card (continuousH2 (r' q F g) (MuΩ q p F g)) := Nat.card_le_card_of_injective _ hΨ
    _ ≤ Nat.card ↥(Submodule.torsionBy ℤ (continuousH2 (r' q F g) (UnΩ q F g)) (p : ℤ)) :=
        Nat.card_le_card_of_injective e₁ he₁
    _ = p := hY

end P2MBrLocC
p2m_reactivate "P2MW.S_groupCohomology_natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le.P2MBrLocC"

end
p2m_reactivate "P2MW.S_groupCohomology_natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le.P2MBrLocC"

open ExtCitation in
theorem solution
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Finite ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((primeLocalToGlobal q).range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((primeLocalToGlobal q).range.map (MulAut.conj g).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ∧
    Nat.card ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((primeLocalToGlobal q).range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((primeLocalToGlobal q).range.map (MulAut.conj g).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ≤ p := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  exact P2MBrLocC.main (q : ℕ) p F g

end S_groupCohomology_natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le
end P2MW
export P2MW.S_groupCohomology_natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le (solution)
