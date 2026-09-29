-- Prove2me | solution 1 for groupCohomology.exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/1ac515bd-567a-5eec-8a02-683d44f34317

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

open scoped TensorProduct Pointwise

local instance CycBaseKummerKer.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance CycBaseKummerKer.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance CycBaseKummerKer.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
local instance CycBaseKummerKer.normalQbar : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

noncomputable section

namespace CycBaseLES

open groupCohomology

section levels

variable {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)

lemma fixingSubgroup_normal (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [hF : Normal ℚ F] : F.fixingSubgroup.Normal := by
  refine ⟨fun s hs g => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
  intro x hx
  have hgx : g⁻¹ x ∈ F := (IntermediateField.normal_iff_forall_map_le'.1 hF g⁻¹) ⟨x, hx, rfl⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hs _ hgx]
  simp

abbrev levelSubgroup (F : IntermediateField ℚ (AlgebraicClosure ℚ)) : Subgroup G := F.fixingSubgroup.comap r

lemma levelSubgroup_normal (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] : (levelSubgroup r F).Normal :=
  (fixingSubgroup_normal F).comap r

lemma levelSubgroup_finiteIndex (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] [FiniteDimensional ℚ F] :
    (levelSubgroup r F).FiniteIndex := by
  haveI := fixingSubgroup_normal F
  refine ⟨fun h0 => ?_⟩
  rw [Subgroup.index_comap] at h0
  have h1 : F.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]; exact Module.finrank_pos.ne'
  exact h1 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_index_of_normal F.fixingSubgroup r.range))

lemma exists_normal_level {X : Type} {f : G → X} (hf : IsLevelConstantSr₁ r S f) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ Normal ℚ F ∧
      ∀ g s, s ∈ levelSubgroup r F → f (g * s) = f g := by
  obtain ⟨F₀, hF₀, h⟩ := hf
  obtain ⟨F, hle, hF, hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S F₀ hF₀
  exact ⟨F, hF, hN, fun g s hs => h g s (IntermediateField.fixingSubgroup_antitone hle hs)⟩

lemma exists_normal_level₂ {X : Type} {f : G × G → X} (hf : IsLevelConstantSr₂ r S f) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ Normal ℚ F ∧
      ∀ g g' s s', s ∈ levelSubgroup r F → s' ∈ levelSubgroup r F → f (g * s, g' * s') = f (g, g') := by
  obtain ⟨F₀, hF₀, h⟩ := hf
  obtain ⟨F, hle, hF, hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S F₀ hF₀
  exact ⟨F, hF, hN, fun g g' s s' hs hs' =>
    h g g' s s' (IntermediateField.fixingSubgroup_antitone hle hs) (IntermediateField.fixingSubgroup_antitone hle hs')⟩

lemma apply_mul_left_eq {X : Type} {f : G → X} (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]
    (h : ∀ g s, s ∈ levelSubgroup r F → f (g * s) = f g) (g s : G) (hs : s ∈ levelSubgroup r F) : f (s * g) = f g := by
  haveI := levelSubgroup_normal r F
  have h1 : g⁻¹ * s * g ∈ levelSubgroup r F := by
    have := Subgroup.Normal.conj_mem inferInstance s hs g⁻¹
    rwa [inv_inv] at this
  have h2 := h g (g⁻¹ * s * g) h1
  rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h2

private lemma _root_.CycBaseLES.finite_range {X : Type} {f : G → X} (hf : IsLevelConstantSr₁ r S f) : (Set.range f).Finite := by
  obtain ⟨F, hF, hN, h⟩ := exists_normal_level r S hf
  haveI := hN
  haveI : FiniteDimensional ℚ ↥F := hF.1
  haveI := levelSubgroup_normal r F
  haveI := levelSubgroup_finiteIndex r F
  haveI : Finite (G ⧸ levelSubgroup r F) := Subgroup.finite_quotient_of_finiteIndex

  let fbar : G ⧸ levelSubgroup r F → X := Quotient.lift f (fun a b hab => by
    have hab' : a⁻¹ * b ∈ levelSubgroup r F := QuotientGroup.leftRel_apply.mp hab
    have := h a (a⁻¹ * b) hab'
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hrange : Set.range f ⊆ Set.range fbar := by
    rintro _ ⟨g, rfl⟩; exact ⟨QuotientGroup.mk g, rfl⟩
  exact (Set.finite_range fbar).subset hrange

p2m_export "CycBaseLES" "finite_range"
end levels

section smooth

variable {k : Type} [CommRing k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (E : Rep.{0} k G)

lemma exists_level_forall_fixed (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a))
    (T : Set E) (hT : T.Finite) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ Normal ℚ F ∧
      ∀ a ∈ T, ∀ s ∈ levelSubgroup r F, E.ρ s a = a := by
  classical
  induction T, hT using Set.Finite.induction_on with
  | empty =>
    obtain ⟨F, -, hF, hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S ⊥ (IntermediateField.isUnramifiedOutside_bot S)
    exact ⟨F, hF, hN, fun a ha => absurd ha (Set.notMem_empty a)⟩
  | @insert a T haT hT ih =>
    obtain ⟨F₁, hF₁, -, h₁⟩ := ih
    obtain ⟨F₂, hF₂, h₂⟩ := hsm a
    obtain ⟨F, hle, hF, hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S (F₁ ⊔ F₂) (hF₁.sup hF₂)
    refine ⟨F, hF, hN, fun b hb s hs => ?_⟩
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · have h3 := h₂ 1 s (IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hle) hs)
      simp only [one_mul, map_one, Module.End.one_apply] at h3
      exact h3
    · exact h₁ b hb s (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hle) hs)

lemma isLevelConstantSr₂_d₁₂ (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a)) {b : G → E}
    (hb : IsLevelConstantSr₁ r S b) : IsLevelConstantSr₂ r S ((d₁₂ E).hom b) := by
  obtain ⟨F₁, hF₁, hN₁, h₁⟩ := exists_normal_level r S hb
  obtain ⟨F₂, hF₂, -, h₂⟩ := exists_level_forall_fixed r S E hsm (Set.range b) (finite_range r S hb)
  haveI := hN₁
  refine ⟨F₁ ⊔ F₂, hF₁.sup hF₂, fun g g' s s' hs hs' => ?_⟩
  have hs₁ : s ∈ levelSubgroup r F₁ := IntermediateField.fixingSubgroup_antitone le_sup_left hs
  have hs'₁ : s' ∈ levelSubgroup r F₁ := IntermediateField.fixingSubgroup_antitone le_sup_left hs'
  have hs₂ : s ∈ levelSubgroup r F₂ := IntermediateField.fixingSubgroup_antitone le_sup_right hs
  rw [d₁₂_hom_apply, d₁₂_hom_apply]
  show E.ρ (g * s) (b (g' * s')) - b (g * s * (g' * s')) + b (g * s) = E.ρ g (b g') - b (g * g') + b g
  rw [h₁ g' s' hs'₁, h₁ g s hs₁, map_mul, Module.End.mul_apply, h₂ (b g') ⟨g', rfl⟩ s hs₂]
  congr 2

  rw [show g * s * (g' * s') = g * g' * (g'⁻¹ * s * g') * s' by group]
  haveI := levelSubgroup_normal r F₁
  have hc : g'⁻¹ * s * g' ∈ levelSubgroup r F₁ := by
    have := Subgroup.Normal.conj_mem inferInstance s hs₁ g'⁻¹; rwa [inv_inv] at this
  rw [h₁ _ s' hs'₁, h₁ _ _ hc]

variable (p : ℕ)

lemma exists_lift (hdiv : ∀ x : E, ∃ y : E, (p : k) • y = x) {c : G → E} (hc : IsLevelConstantSr₁ r S c) :
    ∃ b : G → E, IsLevelConstantSr₁ r S b ∧ ∀ g, (p : k) • b g = c g := by
  choose sec hsec using hdiv
  exact ⟨sec ∘ c, hc.comp sec, fun g => hsec (c g)⟩

lemma cocycle_level {c : G → E} (hc : c ∈ cocycles₁ E) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]
    (h : ∀ g s, s ∈ levelSubgroup r F → c (g * s) = c g) :
    (∀ s ∈ levelSubgroup r F, c s = 0) ∧ ∀ g, ∀ s ∈ levelSubgroup r F, E.ρ s (c g) = c g := by
  have h0 : ∀ s ∈ levelSubgroup r F, c s = 0 := by
    intro s hs
    have h1 := h 1 s hs
    rw [one_mul, cocycles₁_map_one ⟨c, hc⟩ |> fun e => (show c 1 = 0 from e)] at h1
    exact h1
  refine ⟨h0, fun g s hs => ?_⟩
  have h1 := (mem_cocycles₁_iff c).mp hc s g
  rw [apply_mul_left_eq r F h g s hs, h0 s hs, add_zero] at h1
  exact h1.symm

end smooth

end CycBaseLES

end

noncomputable section

namespace CycBaseLES

open groupCohomology

variable {k : Type} [CommRing k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (E : Rep.{0} k G) (p : ℕ)

private def _root_.CycBaseLES.val (t : repTorsionP p E) : E := t.1

p2m_export "CycBaseLES" "val"
lemma val_ρ (g : G) (t : repTorsionP p E) : val E p ((repTorsionP p E).ρ g t) = E.ρ g (val E p t) := rfl

lemma p_smul_val (t : repTorsionP p E) : (p : k) • val E p t = 0 := (Submodule.mem_torsionBy_iff _ _).mp t.2

lemma val_injective : Function.Injective (val E p) := fun _ _ h => Subtype.ext h

lemma val_add (t t' : repTorsionP p E) : val E p (t + t') = val E p t + val E p t' := rfl
lemma val_sub (t t' : repTorsionP p E) : val E p (t - t') = val E p t - val E p t' := rfl
lemma val_zero : val E p (0 : repTorsionP p E) = 0 := rfl

def mkT (e : E) (he : (p : k) • e = 0) : repTorsionP p E := ⟨e, (Submodule.mem_torsionBy_iff _ _).mpr he⟩

@[scoped simp] lemma val_mkT (e : E) (he : (p : k) • e = 0) : val E p (mkT E p e he) = e := rfl

def incl₁ (b : G → repTorsionP p E) : G → E := fun g => val E p (b g)

def incl₂ (z : G × G → repTorsionP p E) : G × G → E := fun x => val E p (z x)

@[scoped simp] lemma incl₁_apply (b : G → repTorsionP p E) (g : G) : incl₁ E p b g = val E p (b g) := rfl

@[scoped simp] lemma incl₂_apply (z : G × G → repTorsionP p E) (x : G × G) : incl₂ E p z x = val E p (z x) := rfl

lemma incl₂_add (z z' : G × G → repTorsionP p E) : incl₂ E p (z + z') = incl₂ E p z + incl₂ E p z' :=
  funext fun _ => rfl

lemma incl₂_injective : Function.Injective (incl₂ E p) := fun z z' h => funext fun x => val_injective E p (congrFun h x)

lemma p_smul_incl₂ (z : G × G → repTorsionP p E) : (p : k) • incl₂ E p z = 0 := by
  funext x; exact p_smul_val E p (z x)

lemma incl₂_d₁₂ (b : G → repTorsionP p E) :
    incl₂ E p ((d₁₂ (repTorsionP p E)).hom b) = (d₁₂ E).hom (incl₁ E p b) := by
  funext x
  rfl

lemma incl₂_mem_cocycles₂ {z : G × G → repTorsionP p E} (hz : z ∈ cocycles₂ (repTorsionP p E)) :
    incl₂ E p z ∈ cocycles₂ E := by
  rw [mem_cocycles₂_iff] at hz ⊢
  intro g h j
  have h1 := congrArg (val E p) (hz g h j)
  exact h1

lemma incl₂_mem_levelCocyclesSr₂ {z : G × G → repTorsionP p E}
    (hz : z ∈ levelCocyclesSr₂ r S (repTorsionP p E)) : incl₂ E p z ∈ levelCocyclesSr₂ r S E :=
  ⟨incl₂_mem_cocycles₂ E p hz.1, hz.2.comp _⟩

lemma incl₂_mem_levelCoboundariesSr₂ {z : G × G → repTorsionP p E}
    (hz : z ∈ levelCoboundariesSr₂ r S (repTorsionP p E)) : incl₂ E p z ∈ levelCoboundariesSr₂ r S E := by
  obtain ⟨b, hb, rfl⟩ := (mem_levelCoboundariesSr₂_iff r S _ _).mp hz
  exact (mem_levelCoboundariesSr₂_iff r S E _).mpr ⟨incl₁ E p b, hb.comp _, (incl₂_d₁₂ E p b).symm⟩

def inclCoc (z : ↥(levelCocyclesSr₂ r S (repTorsionP p E))) : ↥(levelCocyclesSr₂ r S E) :=
  ⟨incl₂ E p z, incl₂_mem_levelCocyclesSr₂ r S E p z.2⟩

lemma inclCoc_add (z z' : ↥(levelCocyclesSr₂ r S (repTorsionP p E))) :
    inclCoc r S E p (z + z') = inclCoc r S E p z + inclCoc r S E p z' := Subtype.ext (incl₂_add E p _ _)

lemma p_smul_inclCoc (z : ↥(levelCocyclesSr₂ r S (repTorsionP p E))) : (p : k) • inclCoc r S E p z = 0 :=
  Subtype.ext (p_smul_incl₂ E p z)

def ιcoc₀ : ↥(levelCocyclesSr₂ r S (repTorsionP p E)) →+ continuousH2Sr r S E where
  toFun z := continuousH2Srπ r S E (inclCoc r S E p z)
  map_zero' := by
    have h : inclCoc r S E p 0 = 0 := Subtype.ext (funext fun _ => rfl)
    show continuousH2Srπ r S E (inclCoc r S E p 0) = 0
    rw [h, map_zero]
  map_add' z z' := by
    show continuousH2Srπ r S E (inclCoc r S E p (z + z')) = _
    rw [inclCoc_add, map_add]

lemma ιcoc₀_apply (z : ↥(levelCocyclesSr₂ r S (repTorsionP p E))) :
    ιcoc₀ r S E p z = continuousH2Srπ r S E (inclCoc r S E p z) := rfl

lemma p_smul_ιcoc₀ (z : ↥(levelCocyclesSr₂ r S (repTorsionP p E))) : (p : k) • ιcoc₀ r S E p z = 0 := by
  rw [ιcoc₀_apply, ← map_smul, p_smul_inclCoc, map_zero]

variable [Fact p.Prime]

def ιcoc : ↥(levelCocyclesSr₂ r S (repTorsionP p E)) →+ ↥(Submodule.torsionBy k (continuousH2Sr r S E) (p : k)) where
  toFun z := ⟨ιcoc₀ r S E p z, (Submodule.mem_torsionBy_iff _ _).mpr (p_smul_ιcoc₀ r S E p z)⟩
  map_zero' := Subtype.ext (ιcoc₀ r S E p).map_zero
  map_add' z z' := Subtype.ext ((ιcoc₀ r S E p).map_add z z')

def ιStar : continuousH2Sr r S (repTorsionP p E) →ₗ[ZMod p] ↥(Submodule.torsionBy k (continuousH2Sr r S E) (p : k)) :=
  Submodule.liftQ _ ((ιcoc r S E p).toZModLinearMap p) (by
    intro z hz
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show continuousH2Srπ r S E (inclCoc r S E p z) = 0
    rw [continuousH2Srπ_eq_zero_iff]
    exact incl₂_mem_levelCoboundariesSr₂ r S E p (Submodule.mem_comap.mp hz))

lemma ιStar_mk (z : ↥(levelCocyclesSr₂ r S (repTorsionP p E))) :
    (ιStar r S E p (continuousH2Srπ r S _ z) : continuousH2Sr r S E) = continuousH2Srπ r S E (inclCoc r S E p z) := rfl

end CycBaseLES
p2m_reactivate "P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.CycBaseLES"

end
p2m_reactivate "P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.CycBaseLES"

noncomputable section

namespace CycBaseLES

open groupCohomology

section delta

variable {k : Type} [CommRing k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (E : Rep.{0} k G) (p : ℕ)

lemma mem_cocycles₂_of_incl₂ {z : G × G → repTorsionP p E} (h : incl₂ E p z ∈ cocycles₂ E) : z ∈ cocycles₂ (repTorsionP p E) := by
  rw [mem_cocycles₂_iff] at h ⊢
  intro g i j
  exact val_injective E p (h g i j)

omit [CommRing k] in
lemma isLevelConstantSr₂_of_comp_injective {X Y : Type} {f : G × G → X} {φ : X → Y} (hφ : Function.Injective φ)
    (h : IsLevelConstantSr₂ r S (φ ∘ f)) : IsLevelConstantSr₂ r S f := by
  obtain ⟨F, hF, h⟩ := h
  exact ⟨F, hF, fun g g' s s' hs hs' => hφ (h g g' s s' hs hs')⟩

omit [CommRing k] in
lemma isLevelConstantSr₁_of_comp_injective {X Y : Type} {f : G → X} {φ : X → Y} (hφ : Function.Injective φ)
    (h : IsLevelConstantSr₁ r S (φ ∘ f)) : IsLevelConstantSr₁ r S f := by
  obtain ⟨F, hF, h⟩ := h
  exact ⟨F, hF, fun g s hs => hφ (h g s hs)⟩

lemma p_smul_d₁₂_eq_zero {b c : G → E} (hc : c ∈ cocycles₁ E) (hpb : ∀ g, (p : k) • b g = c g) (x : G × G) :
    (p : k) • (d₁₂ E).hom b x = 0 := by
  have h1 : (p : k) • b = c := funext hpb
  have h2 : (d₁₂ E).hom c = 0 := LinearMap.mem_ker.mp hc
  have h3 := congrFun (congrArg (d₁₂ E).hom h1) x
  rw [map_smul, Pi.smul_apply, h2, Pi.zero_apply] at h3
  exact h3

def rep (x : ↥(continuousH1Sr r S E)) : ↥(levelCocyclesSr₁ r S E) :=
  ⟨Classical.choose ((mem_continuousH1Sr_iff r S E x.1).mp x.2), (Classical.choose_spec ((mem_continuousH1Sr_iff r S E x.1).mp x.2)).1⟩

lemma H1π_rep (x : ↥(continuousH1Sr r S E)) : (H1π E).hom (rep r S E x).1 = x.1 :=
  (Classical.choose_spec ((mem_continuousH1Sr_iff r S E x.1).mp x.2)).2

variable (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a))
include hsm

def dT (b : G → E) (hb : IsLevelConstantSr₁ r S b) (hpb : ∀ x, (p : k) • (d₁₂ E).hom b x = 0) :
    ↥(levelCocyclesSr₂ r S (repTorsionP p E)) :=
  ⟨fun x => mkT E p ((d₁₂ E).hom b x) (hpb x), by
    refine ⟨mem_cocycles₂_of_incl₂ E p ?_, ?_⟩
    · exact d₁₂_apply_mem_cocycles₂ b
    · exact isLevelConstantSr₂_of_comp_injective r S (f := fun x => mkT E p ((d₁₂ E).hom b x) (hpb x))
        (val_injective E p) (isLevelConstantSr₂_d₁₂ r S E hsm hb)⟩

lemma incl₂_dT (b : G → E) (hb : IsLevelConstantSr₁ r S b) (hpb : ∀ x, (p : k) • (d₁₂ E).hom b x = 0) :
    incl₂ E p (dT r S E p hsm b hb hpb) = (d₁₂ E).hom b := rfl

lemma dT_sub_mem (b b' : G → E) (hb : IsLevelConstantSr₁ r S b) (hb' : IsLevelConstantSr₁ r S b')
    (hpb : ∀ x, (p : k) • (d₁₂ E).hom b x = 0) (hpb' : ∀ x, (p : k) • (d₁₂ E).hom b' x = 0)
    (heq : ∀ g, (p : k) • b g = (p : k) • b' g) :
    ((dT r S E p hsm b hb hpb - dT r S E p hsm b' hb' hpb' : ↥(levelCocyclesSr₂ r S (repTorsionP p E))) : G × G → repTorsionP p E) ∈
      levelCoboundariesSr₂ r S (repTorsionP p E) := by

  have hpt : ∀ g, (p : k) • (b - b') g = 0 := fun g => by rw [Pi.sub_apply, smul_sub, heq g, sub_self]
  let t : G → repTorsionP p E := fun g => mkT E p ((b - b') g) (hpt g)
  have hbb : IsLevelConstantSr₁ r S (b - b') := by
    have h2 : b - b' = b + (fun e : E => -e) ∘ b' := by funext g; simp [sub_eq_add_neg]
    rw [h2]; exact hb.add (hb'.comp _)
  have ht : IsLevelConstantSr₁ r S t := isLevelConstantSr₁_of_comp_injective r S (f := t) (val_injective E p) hbb
  refine (mem_levelCoboundariesSr₂_iff r S _ _).mpr ⟨t, ht, ?_⟩
  apply incl₂_injective E p
  rw [incl₂_d₁₂]
  show (d₁₂ E).hom (b - b') = incl₂ E p (dT r S E p hsm b hb hpb - dT r S E p hsm b' hb' hpb')
  rw [map_sub]
  rfl

variable (hdiv : ∀ x : E, ∃ y : E, (p : k) • y = x)
include hdiv

def δcoc (c : ↥(levelCocyclesSr₁ r S E)) : continuousH2Sr r S (repTorsionP p E) :=
  continuousH2Srπ r S _ (dT r S E p hsm (Classical.choose (exists_lift r S E p hdiv c.2))
    (Classical.choose_spec (exists_lift r S E p hdiv c.2)).1
    (p_smul_d₁₂_eq_zero E p c.1.2 (Classical.choose_spec (exists_lift r S E p hdiv c.2)).2))

lemma δcoc_spec (c : ↥(levelCocyclesSr₁ r S E)) (b : G → E) (hb : IsLevelConstantSr₁ r S b) (hpb : ∀ g, (p : k) • b g = c.1 g) :
    δcoc r S E p hsm hdiv c = continuousH2Srπ r S _ (dT r S E p hsm b hb (p_smul_d₁₂_eq_zero E p c.1.2 hpb)) := by
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact dT_sub_mem r S E p hsm _ _ _ _ _ _ (fun g => ((Classical.choose_spec (exists_lift r S E p hdiv c.2)).2 g).trans (hpb g).symm)

lemma δcoc_add (c c' : ↥(levelCocyclesSr₁ r S E)) :
    δcoc r S E p hsm hdiv (c + c') = δcoc r S E p hsm hdiv c + δcoc r S E p hsm hdiv c' := by
  obtain ⟨b, hb, hpb⟩ := exists_lift r S E p hdiv c.2
  obtain ⟨b', hb', hpb'⟩ := exists_lift r S E p hdiv c'.2
  rw [δcoc_spec r S E p hsm hdiv c b hb hpb, δcoc_spec r S E p hsm hdiv c' b' hb' hpb',
    δcoc_spec r S E p hsm hdiv (c + c') (b + b') (hb.add hb') (fun g => by
      show (p : k) • (b g + b' g) = (c.1 : G → E) g + (c'.1 : G → E) g
      rw [smul_add, hpb, hpb']; rfl),
    ← map_add]
  congr 1
  apply Subtype.ext; funext x; apply val_injective E p
  show (d₁₂ E).hom (b + b') x = (d₁₂ E).hom b x + (d₁₂ E).hom b' x
  rw [map_add]; rfl

lemma δcoc_eq_of_H1π_eq (c c' : ↥(levelCocyclesSr₁ r S E)) (h : (H1π E).hom c.1 = (H1π E).hom c'.1) :
    δcoc r S E p hsm hdiv c = δcoc r S E p hsm hdiv c' := by
  have h1 : (c.1 : G → E) - (c'.1 : G → E) ∈ coboundaries₁ E := (H1π_eq_iff c.1 c'.1).mp h
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp h1
  obtain ⟨a₁, ha₁⟩ := hdiv a
  obtain ⟨b', hb', hpb'⟩ := exists_lift r S E p hdiv c'.2

  have hlc : IsLevelConstantSr₁ r S ((d₀₁ E).hom a₁) := by
    have h2 : ((d₀₁ E).hom a₁ : G → E) = (fun g => E.ρ g a₁) + fun _ => -a₁ := by
      funext g; rw [d₀₁_hom_apply, Pi.add_apply, sub_eq_add_neg]
    rw [h2]
    exact (hsm a₁).add (isLevelConstantSr₁_const r S (-a₁))
  have hpb : ∀ g, (p : k) • (b' + (d₀₁ E).hom a₁) g = c.1 g := by
    intro g
    have h3 := congrFun ha g
    rw [Pi.sub_apply] at h3
    rw [Pi.add_apply, smul_add, hpb', ← Pi.smul_apply, ← map_smul, ha₁, h3]
    show (c'.1 : G → E) g + ((c.1 : G → E) g - (c'.1 : G → E) g) = (c.1 : G → E) g
    abel
  rw [δcoc_spec r S E p hsm hdiv c' b' hb' hpb', δcoc_spec r S E p hsm hdiv c _ (hb'.add hlc) hpb]
  congr 1
  apply Subtype.ext; funext x; apply val_injective E p
  show (d₁₂ E).hom (b' + (d₀₁ E).hom a₁) x = (d₁₂ E).hom b' x
  rw [map_add, Pi.add_apply, d₀₁_comp_d₁₂_apply, Pi.zero_apply, add_zero]

lemma δcoc_p_smul (c : ↥(levelCocyclesSr₁ r S E)) : δcoc r S E p hsm hdiv ((p : k) • c) = 0 := by
  rw [δcoc_spec r S E p hsm hdiv ((p : k) • c) (c.1 : G → E) c.2 (fun g => rfl)]
  convert map_zero (continuousH2Srπ r S (repTorsionP p E))
  apply Subtype.ext; funext x; apply val_injective E p
  show (d₁₂ E).hom (c.1 : G → E) x = 0
  rw [show (d₁₂ E).hom (c.1 : G → E) = 0 from LinearMap.mem_ker.mp c.1.2]
  rfl

def δX : ↥(continuousH1Sr r S E) →+ continuousH2Sr r S (repTorsionP p E) where
  toFun x := δcoc r S E p hsm hdiv (rep r S E x)
  map_zero' := by
    have h : (H1π E).hom (rep r S E 0).1 = (H1π E).hom (0 : ↥(levelCocyclesSr₁ r S E)).1 := by
      rw [H1π_rep]; exact (map_zero _).symm
    rw [δcoc_eq_of_H1π_eq r S E p hsm hdiv _ _ h]
    have h0 : (0 : ↥(levelCocyclesSr₁ r S E)) = (p : k) • (0 : ↥(levelCocyclesSr₁ r S E)) := (smul_zero _).symm
    rw [h0]; exact δcoc_p_smul r S E p hsm hdiv 0
  map_add' x y := by
    have h : (H1π E).hom (rep r S E (x + y)).1 = (H1π E).hom (rep r S E x + rep r S E y).1 := by
      rw [H1π_rep]
      show x.1 + y.1 = (H1π E).hom ((rep r S E x).1 + (rep r S E y).1)
      rw [map_add, H1π_rep, H1π_rep]
    show δcoc r S E p hsm hdiv (rep r S E (x + y)) = δcoc r S E p hsm hdiv (rep r S E x) + δcoc r S E p hsm hdiv (rep r S E y)
    rw [δcoc_eq_of_H1π_eq r S E p hsm hdiv _ _ h, δcoc_add]

lemma δX_mk (c : ↥(levelCocyclesSr₁ r S E)) :
    δX r S E p hsm hdiv ⟨(H1π E).hom c.1, H1π_mem_continuousH1Sr r S E c.2⟩ = δcoc r S E p hsm hdiv c :=
  δcoc_eq_of_H1π_eq r S E p hsm hdiv _ _ (H1π_rep r S E _)

lemma δX_p_smul (x : ↥(continuousH1Sr r S E)) : δX r S E p hsm hdiv ((p : k) • x) = 0 := by
  have h : (H1π E).hom (rep r S E ((p : k) • x)).1 = (H1π E).hom ((p : k) • rep r S E x).1 := by
    rw [H1π_rep]
    show (p : k) • x.1 = (H1π E).hom ((p : k) • (rep r S E x).1)
    rw [map_smul, H1π_rep]
  show δcoc r S E p hsm hdiv (rep r S E ((p : k) • x)) = 0
  rw [δcoc_eq_of_H1π_eq r S E p hsm hdiv _ _ h, δcoc_p_smul]

variable [Fact p.Prime]

def δbar : (↥(continuousH1Sr r S E) ⧸ ((p : k) • (⊤ : Submodule k ↥(continuousH1Sr r S E)))) →ₗ[ZMod p]
    continuousH2Sr r S (repTorsionP p E) :=
  AddMonoidHom.toZModLinearMap p
    (QuotientAddGroup.lift ((p : k) • (⊤ : Submodule k ↥(continuousH1Sr r S E))).toAddSubgroup (δX r S E p hsm hdiv) (by
      rintro x hx
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      exact δX_p_smul r S E p hsm hdiv y))

lemma δbar_mk (x : ↥(continuousH1Sr r S E)) : δbar r S E p hsm hdiv (Submodule.Quotient.mk x) = δX r S E p hsm hdiv x := rfl

end delta
p2m_reactivate "P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.CycBaseLES"

end CycBaseLES
p2m_reactivate "P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.CycBaseLES"

end
p2m_reactivate "P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.CycBaseLES"

noncomputable section

namespace CycBaseLES

open groupCohomology

section exact

variable {k : Type} [CommRing k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (E : Rep.{0} k G) (p : ℕ) [Fact p.Prime]
  (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a)) (hdiv : ∀ x : E, ∃ y : E, (p : k) • y = x)
include hsm hdiv

lemma range_δbar_eq_ker_ιStar : LinearMap.range (δbar r S E p hsm hdiv) = LinearMap.ker (ιStar r S E p) := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [LinearMap.mem_ker, δbar_mk]
    obtain ⟨b, hb, hpb⟩ := exists_lift r S E p hdiv (rep r S E x).2
    show ιStar r S E p (δcoc r S E p hsm hdiv (rep r S E x)) = 0
    rw [δcoc_spec r S E p hsm hdiv _ b hb hpb]
    apply Subtype.ext
    rw [ιStar_mk]
    show continuousH2Srπ r S E (inclCoc r S E p _) = 0
    rw [continuousH2Srπ_eq_zero_iff]
    exact (mem_levelCoboundariesSr₂_iff r S E _).mpr ⟨b, hb, rfl⟩
  · intro y hy
    obtain ⟨z, rfl⟩ := continuousH2Srπ_surjective r S (repTorsionP p E) y
    rw [LinearMap.mem_ker] at hy
    have hy' : continuousH2Srπ r S E (inclCoc r S E p z) = 0 := congrArg Subtype.val hy
    rw [continuousH2Srπ_eq_zero_iff] at hy'
    obtain ⟨b, hb, hbz⟩ := (mem_levelCoboundariesSr₂_iff r S E _).mp hy'

    have hc : ((p : k) • b) ∈ cocycles₁ E := by
      change ((p : k) • b) ∈ LinearMap.ker (d₁₂ E).hom
      rw [LinearMap.mem_ker, map_smul, hbz]
      exact p_smul_incl₂ E p z
    let c : ↥(levelCocyclesSr₁ r S E) := ⟨⟨(p : k) • b, hc⟩, hb.comp _⟩
    refine ⟨Submodule.Quotient.mk ⟨(H1π E).hom c.1, H1π_mem_continuousH1Sr r S E c.2⟩, ?_⟩
    rw [δbar_mk, δX_mk, δcoc_spec r S E p hsm hdiv c b hb (fun g => rfl)]
    congr 1
    apply Subtype.ext
    apply incl₂_injective E p
    rw [incl₂_dT]
    exact hbz

lemma ιStar_surjective : Function.Surjective (ιStar r S E p) := by
  intro w
  obtain ⟨z, hz⟩ := continuousH2Srπ_surjective r S E (w : continuousH2Sr r S E)
  have hpw : (p : k) • (w : continuousH2Sr r S E) = 0 := (Submodule.mem_torsionBy_iff _ _).mp w.2
  rw [← hz, ← map_smul, continuousH2Srπ_eq_zero_iff] at hpw
  obtain ⟨b, hb, hbz⟩ := (mem_levelCoboundariesSr₂_iff r S E _).mp hpw
  obtain ⟨b', hb', hpb'⟩ := exists_lift r S E p hdiv hb

  have hz' : ∀ x, (p : k) • ((z : G × G → E) - (d₁₂ E).hom b') x = 0 := by
    intro x
    have h1 : (p : k) • b' = b := funext hpb'
    have h2 := congrFun hbz x
    rw [Pi.sub_apply, smul_sub, ← Pi.smul_apply ((p : k)) ((d₁₂ E).hom b'), ← map_smul, h1, h2]
    exact sub_self _
  let zT : G × G → repTorsionP p E := fun x => mkT E p (((z : G × G → E) - (d₁₂ E).hom b') x) (hz' x)
  have hinclT : incl₂ E p zT = (z : G × G → E) - (d₁₂ E).hom b' := rfl
  have hmem : zT ∈ levelCocyclesSr₂ r S (repTorsionP p E) := by
    refine ⟨mem_cocycles₂_of_incl₂ E p ?_, isLevelConstantSr₂_of_comp_injective r S (f := zT) (val_injective E p) ?_⟩
    · rw [hinclT]; exact Submodule.sub_mem _ z.2.1 (d₁₂_apply_mem_cocycles₂ b')
    · show IsLevelConstantSr₂ r S (incl₂ E p zT)
      rw [hinclT, sub_eq_add_neg]
      exact z.2.2.add ((isLevelConstantSr₂_d₁₂ r S E hsm hb').comp (fun e : E => -e))
  refine ⟨continuousH2Srπ r S _ ⟨zT, hmem⟩, ?_⟩
  apply Subtype.ext
  rw [ιStar_mk, ← hz]
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  refine (mem_levelCoboundariesSr₂_iff r S E _).mpr ⟨-b', hb'.comp (fun e : E => -e), ?_⟩
  rw [map_neg]
  show -(d₁₂ E).hom b' = incl₂ E p zT - (z : G × G → E)
  rw [hinclT]; abel

lemma δbar_injective : Function.Injective (δbar r S E p hsm hdiv) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [δbar_mk] at hu
  obtain ⟨b, hb, hpb⟩ := exists_lift r S E p hdiv (rep r S E x).2
  have hu' : δcoc r S E p hsm hdiv (rep r S E x) = 0 := hu
  rw [δcoc_spec r S E p hsm hdiv _ b hb hpb, continuousH2Srπ_eq_zero_iff] at hu'
  obtain ⟨t, ht, htd⟩ := (mem_levelCoboundariesSr₂_iff r S _ _).mp hu'

  have hd : (d₁₂ E).hom (b - incl₁ E p t) = 0 := by
    rw [map_sub, ← incl₂_d₁₂, htd, incl₂_dT, sub_self]
  have hb₂ : (b - incl₁ E p t) ∈ cocycles₁ E := LinearMap.mem_ker.mpr hd
  have hlc₂ : IsLevelConstantSr₁ r S (b - incl₁ E p t) := by
    rw [sub_eq_add_neg]; exact hb.add ((ht.comp (val E p)).comp (fun e : E => -e))
  let c₂ : ↥(levelCocyclesSr₁ r S E) := ⟨⟨b - incl₁ E p t, hb₂⟩, hlc₂⟩
  have hpc₂ : (p : k) • c₂ = rep r S E x := by
    apply Subtype.ext; apply Subtype.ext; funext g
    show (p : k) • (b - incl₁ E p t) g = ((rep r S E x).1 : G → E) g
    rw [Pi.sub_apply, smul_sub, hpb, incl₁_apply, p_smul_val, sub_zero]
    rfl

  have hx : x = (p : k) • (⟨(H1π E).hom c₂.1, H1π_mem_continuousH1Sr r S E c₂.2⟩ : ↥(continuousH1Sr r S E)) := by
    apply Subtype.ext
    show x.1 = (p : k) • (H1π E).hom c₂.1
    rw [← map_smul, ← H1π_rep r S E x, ← hpc₂]
    rfl
  rw [hx]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)

theorem finrank_eq :
    (FiniteDimensional (ZMod p) (continuousH2Sr r S (repTorsionP p E)) ↔
        (FiniteDimensional (ZMod p) (↥(continuousH1Sr r S E) ⧸ ((p : k) • (⊤ : Submodule k ↥(continuousH1Sr r S E)))) ∧
          FiniteDimensional (ZMod p) ↥(Submodule.torsionBy k (continuousH2Sr r S E) (p : k)))) ∧
      (FiniteDimensional (ZMod p) (continuousH2Sr r S (repTorsionP p E)) →
        Module.finrank (ZMod p) (continuousH2Sr r S (repTorsionP p E)) =
          Module.finrank (ZMod p) (↥(continuousH1Sr r S E) ⧸ ((p : k) • (⊤ : Submodule k ↥(continuousH1Sr r S E)))) +
            Module.finrank (ZMod p) ↥(Submodule.torsionBy k (continuousH2Sr r S E) (p : k))) := by
  have hinj := δbar_injective r S E p hsm hdiv
  have hsurj := ιStar_surjective r S E p hsm hdiv
  have hex := range_δbar_eq_ker_ιStar r S E p hsm hdiv
  refine ⟨⟨fun hV => ⟨Module.Finite.of_injective _ hinj, Module.Finite.of_surjective _ hsurj⟩, fun ⟨hU, hW⟩ => ?_⟩, fun hV => ?_⟩
  ·
    haveI : Module.Finite (ZMod p) ↥(LinearMap.ker (ιStar r S E p)) := by
      rw [← hex]; exact Module.Finite.of_surjective _ (LinearMap.surjective_rangeRestrict _)
    haveI : Module.Finite (ZMod p) (continuousH2Sr r S (repTorsionP p E) ⧸ LinearMap.ker (ιStar r S E p)) :=
      Module.Finite.equiv ((ιStar r S E p).quotKerEquivOfSurjective hsurj).symm
    exact Module.Finite.of_submodule_quotient (LinearMap.ker (ιStar r S E p))
  · haveI := hV
    have h1 := (ιStar r S E p).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, ← hex, LinearMap.finrank_range_of_inj hinj] at h1
    omega

end exact
p2m_reactivate "P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.CycBaseLES"

end CycBaseLES
p2m_reactivate "P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.CycBaseLES"

end
p2m_reactivate "P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.CycBaseLES"

noncomputable section

namespace CycBaseLES

open groupCohomology

section maps

variable {k : Type} [CommRing k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (E : Rep.{0} k G) (p : ℕ) [Fact p.Prime]
  (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a)) (hdiv : ∀ x : E, ∃ y : E, (p : k) • y = x)
include hsm hdiv

theorem maps :
    ∃ (δ : ↥(continuousH1Sr r S E) →+ continuousH2Sr r S (repTorsionP p E))
      (ι : continuousH2Sr r S (repTorsionP p E) →+ continuousH2Sr r S E),
      (∀ x : ↥(continuousH1Sr r S E), δ x = 0 ↔ ∃ y : ↥(continuousH1Sr r S E), x = p • y) ∧
      (∀ v : continuousH2Sr r S (repTorsionP p E), ι v = 0 ↔ ∃ x, δ x = v) ∧
      (∀ w : continuousH2Sr r S E, (∃ v, ι v = w) ↔ p • w = 0) ∧
      (∀ z : ↥(levelCocyclesSr₂ r S (repTorsionP p E)),
        ∃ hz : (fun x : G × G => ((z : G × G → repTorsionP p E) x).1) ∈ levelCocyclesSr₂ r S E,
          ι (continuousH2Srπ r S (repTorsionP p E) z) = continuousH2Srπ r S E ⟨_, hz⟩) ∧
      (∀ (c : ↥(levelCocyclesSr₁ r S E)) (b : G → E), IsLevelConstantSr₁ r S b → (∀ g, p • b g = (c.1 : G → E) g) →
        ∃ w : ↥(levelCocyclesSr₂ r S (repTorsionP p E)),
          (∀ x : G × G, ((w : G × G → repTorsionP p E) x).1 = (d₁₂ E).hom b x) ∧
          δ ⟨(H1π E).hom c.1, H1π_mem_continuousH1Sr r S E c.2⟩ = continuousH2Srπ r S (repTorsionP p E) w) := by
  refine ⟨δX r S E p hsm hdiv, (Submodule.subtype _).toAddMonoidHom.comp (ιStar r S E p).toAddMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x
    constructor
    · intro hx
      have h := δbar_injective r S E p hsm hdiv (a₁ := Submodule.Quotient.mk x) (a₂ := 0)
        (by rw [δbar_mk, map_zero]; exact hx)
      rw [Submodule.Quotient.mk_eq_zero] at h
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      exact ⟨y, Nat.cast_smul_eq_nsmul k p y⟩
    · rintro ⟨y, rfl⟩
      rw [← Nat.cast_smul_eq_nsmul k p y]
      exact δX_p_smul r S E p hsm hdiv y
  ·
    intro v
    have hex := range_δbar_eq_ker_ιStar r S E p hsm hdiv
    constructor
    · intro hv
      have hv' : v ∈ LinearMap.ker (ιStar r S E p) := by
        rw [LinearMap.mem_ker]; exact Subtype.ext hv
      rw [← hex] at hv'
      obtain ⟨u, hu⟩ := hv'
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
      exact ⟨x, hu⟩
    · rintro ⟨x, rfl⟩
      have hx : δbar r S E p hsm hdiv (Submodule.Quotient.mk x) ∈ LinearMap.ker (ιStar r S E p) := by
        rw [← hex]; exact ⟨_, rfl⟩
      rw [LinearMap.mem_ker, δbar_mk] at hx
      exact congrArg Subtype.val hx
  ·
    intro w
    constructor
    · rintro ⟨v, rfl⟩
      have h := (Submodule.mem_torsionBy_iff _ _).mp (ιStar r S E p v).2
      rw [Nat.cast_smul_eq_nsmul] at h
      exact h
    · intro hw
      have hw' : w ∈ Submodule.torsionBy k (continuousH2Sr r S E) (p : k) := by
        rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]; exact hw
      obtain ⟨v, hv⟩ := ιStar_surjective r S E p hsm hdiv ⟨w, hw'⟩
      exact ⟨v, congrArg Subtype.val hv⟩
  ·
    intro z
    exact ⟨incl₂_mem_levelCocyclesSr₂ r S E p z.2, rfl⟩
  ·
    intro c b hb hpb
    have hpb' : ∀ g, (p : k) • b g = (c.1 : G → E) g := fun g => by rw [Nat.cast_smul_eq_nsmul]; exact hpb g
    exact ⟨dT r S E p hsm b hb (p_smul_d₁₂_eq_zero E p c.1.2 hpb'), fun x => rfl,
      (δX_mk r S E p hsm hdiv c).trans (δcoc_spec r S E p hsm hdiv c b hb hpb')⟩

end maps
p2m_reactivate "P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.CycBaseLES"

end CycBaseLES
p2m_reactivate "P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.CycBaseLES"

end
p2m_reactivate "P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.CycBaseLES"

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) {G : Type} [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (E : Rep.{0} ℤ G)
    (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a))
    (hdiv : ∀ x : E, ∃ y : E, (p : ℤ) • y = x) :
    ∃ (δ : ↥(continuousH1Sr r S E) →+ continuousH2Sr r S (repTorsionP p E))
      (ι : continuousH2Sr r S (repTorsionP p E) →+ continuousH2Sr r S E),
      (∀ x : ↥(continuousH1Sr r S E), δ x = 0 ↔ ∃ y : ↥(continuousH1Sr r S E), x = p • y) ∧
      (∀ v : continuousH2Sr r S (repTorsionP p E), ι v = 0 ↔ ∃ x, δ x = v) ∧
      (∀ w : continuousH2Sr r S E, (∃ v, ι v = w) ↔ p • w = 0) ∧
      (∀ z : ↥(levelCocyclesSr₂ r S (repTorsionP p E)),
        ∃ hz : (fun x : G × G => ((z : G × G → repTorsionP p E) x).1) ∈ levelCocyclesSr₂ r S E,
          ι (continuousH2Srπ r S (repTorsionP p E) z) = continuousH2Srπ r S E ⟨_, hz⟩) ∧
      (∀ (c : ↥(levelCocyclesSr₁ r S E)) (b : G → E), IsLevelConstantSr₁ r S b → (∀ g, p • b g = (c.1 : G → E) g) →
        ∃ w : ↥(levelCocyclesSr₂ r S (repTorsionP p E)),
          (∀ x : G × G, ((w : G × G → repTorsionP p E) x).1 = (d₁₂ E).hom b x) ∧
          δ ⟨(H1π E).hom c.1, H1π_mem_continuousH1Sr r S E c.2⟩ = continuousH2Srπ r S (repTorsionP p E) w) := by
  refine CycBaseLES.maps r S E p hsm (fun x => ?_)
  obtain ⟨y, hy⟩ := hdiv x
  exact ⟨y, (int_smul_eq_zsmul _ _ _).trans hy⟩

end S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible
end P2MW
export P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible (solution)
