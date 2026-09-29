-- Prove2me | solution 1 for groupCohomology.kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/5bfc5cf2-b8ca-5a7d-8215-6296b63bf826

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith TensorProduct Pointwise
set_option maxHeartbeats 1600000
set_option Elab.async false
open IsDedekindDomain
open scoped NumberField

local instance CycBaseKummerKer.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance CycBaseKummerKer.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance CycBaseKummerKer.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
local instance CycBaseKummerKer.normalQbar : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

noncomputable section

namespace CycBaseLES3

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

private lemma _root_.CycBaseLES3.finite_range {X : Type} {f : G → X} (hf : IsLevelConstantSr₁ r S f) : (Set.range f).Finite := by
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

p2m_export "CycBaseLES3" "finite_range"
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

section finlevels

variable {k : Type} [CommRing k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)

def LCF {X : Type} {n : ℕ} (u : (Fin n → G) → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
    ∀ g s : Fin n → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → u (g * s) = u g

variable {r S}

lemma LCF.comp {X Y : Type} {n : ℕ} {u : (Fin n → G) → X} (hu : LCF r S u) (φ : X → Y) : LCF r S (φ ∘ u) := by
  obtain ⟨F, hF, h⟩ := hu
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, h g s hs]⟩

lemma LCF.add {X : Type} [Add X] {n : ℕ} {u u' : (Fin n → G) → X} (hu : LCF r S u) (hu' : LCF r S u') : LCF r S (u + u') := by
  obtain ⟨F, hF, h⟩ := hu
  obtain ⟨F', hF', h'⟩ := hu'
  refine ⟨F ⊔ F', hF.sup hF', fun g s hs => ?_⟩
  simp only [Pi.add_apply]
  rw [h g s fun i => IntermediateField.fixingSubgroup_antitone le_sup_left (hs i),
    h' g s fun i => IntermediateField.fixingSubgroup_antitone le_sup_right (hs i)]

lemma LCF.neg {X : Type} [Neg X] {n : ℕ} {u : (Fin n → G) → X} (hu : LCF r S u) : LCF r S (-u) := by
  obtain ⟨F, hF, h⟩ := hu
  exact ⟨F, hF, fun g s hs => by simp only [Pi.neg_apply, h g s hs]⟩

lemma LCF.sub {X : Type} [AddGroup X] {n : ℕ} {u u' : (Fin n → G) → X} (hu : LCF r S u) (hu' : LCF r S u') : LCF r S (u - u') := by
  rw [sub_eq_add_neg]; exact hu.add hu'.neg

lemma LCF_zero {X : Type} [Zero X] {n : ℕ} : LCF r S (0 : (Fin n → G) → X) := by
  obtain ⟨F, -, hF, -⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S ⊥ (IntermediateField.isUnramifiedOutside_bot S)
  exact ⟨F, hF, fun _ _ _ => rfl⟩

lemma LCF_and {X Y : Type} {n : ℕ} {u : (Fin n → G) → X} {u' : (Fin n → G) → Y} (hu : LCF r S u) (hu' : LCF r S u') :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin n → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → u (g * s) = u g ∧ u' (g * s) = u' g := by
  obtain ⟨F, hF, h⟩ := hu
  obtain ⟨F', hF', h'⟩ := hu'
  exact ⟨F ⊔ F', hF.sup hF', fun g s hs =>
    ⟨h g s fun i => IntermediateField.fixingSubgroup_antitone le_sup_left (hs i),
     h' g s fun i => IntermediateField.fixingSubgroup_antitone le_sup_right (hs i)⟩⟩

def read₁ {X : Type} (f : G → X) : (Fin 1 → G) → X := fun v => f (v 0)
def read₂ {X : Type} (f : G × G → X) : (Fin 2 → G) → X := fun v => f (v 0, v 1)
def unread₂ {X : Type} (b : (Fin 2 → G) → X) : G × G → X := fun x => b ![x.1, x.2]

omit [Group G] in
lemma read₂_unread₂ {X : Type} (b : (Fin 2 → G) → X) : read₂ (unread₂ b) = b := by
  funext v
  simp only [read₂, unread₂]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [Group G] in
lemma unread₂_read₂ {X : Type} (f : G × G → X) : unread₂ (read₂ f) = f := by
  funext x; rfl

lemma LCF_read₂_iff {X : Type} (f : G × G → X) : LCF r S (read₂ f) ↔ IsLevelConstantSr₂ r S f := by
  constructor
  · rintro ⟨F, hF, h⟩
    refine ⟨F, hF, fun g g' s s' hs hs' => ?_⟩
    have := h ![g, g'] ![s, s'] (fun i => by fin_cases i <;> [exact hs; exact hs'])
    simpa [read₂] using this
  · rintro ⟨F, hF, h⟩
    refine ⟨F, hF, fun g s hs => ?_⟩
    simp only [read₂, Pi.mul_apply]
    exact h _ _ _ _ (hs 0) (hs 1)

lemma LCF_read₁_iff {X : Type} (f : G → X) : LCF r S (read₁ f) ↔ IsLevelConstantSr₁ r S f := by
  constructor
  · rintro ⟨F, hF, h⟩
    refine ⟨F, hF, fun g s hs => ?_⟩
    have := h ![g] ![s] (fun i => by fin_cases i; exact hs)
    simpa [read₁] using this
  · rintro ⟨F, hF, h⟩
    refine ⟨F, hF, fun g s hs => ?_⟩
    simp only [read₁, Pi.mul_apply]
    exact h _ _ (hs 0)

lemma LCF_unread₂ {X : Type} {b : (Fin 2 → G) → X} (hb : LCF r S b) : IsLevelConstantSr₂ r S (unread₂ b) := by
  rw [← LCF_read₂_iff, read₂_unread₂]; exact hb

end finlevels

section bridges

variable {k : Type} [CommRing k] {G : Type} [Group G] (E : Rep.{0} k G)

lemma cochainsIso₁_inv_apply (f : G → E) : (cochainsIso₁ E).inv f = read₁ f := rfl

lemma cochainsIso₂_inv_apply (f : G × G → E) : (cochainsIso₂ E).inv f = read₂ f := rfl

lemma d12_read₁ (x : G → E) : ((inhomogeneousCochains E).d 1 2).hom (read₁ x) = read₂ ((d₁₂ E).hom x) := by
  have h := congrArg (fun φ => (ConcreteCategory.hom φ) x) (eq_d₁₂_comp_inv E)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  rw [cochainsIso₁_inv_apply, cochainsIso₂_inv_apply] at h
  exact h

lemma d23_read₂_eq_zero_iff (f : G × G → E) : ((inhomogeneousCochains E).d 2 3).hom (read₂ f) = 0 ↔ f ∈ cocycles₂ E := by
  have h := congrArg (fun φ => (ConcreteCategory.hom φ) f) (eq_d₂₃_comp_inv E)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  rw [cochainsIso₂_inv_apply] at h
  rw [h, cocycles₂, LinearMap.mem_ker]
  constructor
  · intro h0
    have := congrArg (cochainsIso₃ E).hom h0
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply, map_zero] at this
    exact this
  · intro h0
    rw [h0, map_zero]

lemma d23_d12 (x : (Fin 1 → G) → E) :
    ((inhomogeneousCochains E).d 2 3).hom (((inhomogeneousCochains E).d 1 2).hom x) = 0 := by
  have h := (inhomogeneousCochains E).d_comp_d 1 2 3
  have := congrArg (fun φ => (ConcreteCategory.hom φ) x) h
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at this
  exact this

end bridges

section clauses

variable {k : Type} [CommRing k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (E : Rep.{0} k G) (p : ℕ)

abbrev valF {n : ℕ} (e : (Fin n → G) → repTorsionP p E) : (Fin n → G) → E := fun v => ((e v : repTorsionP p E) : E)

lemma p_smul_valF {n : ℕ} (e : (Fin n → G) → repTorsionP p E) : (p : k) • valF E p e = 0 := by
  funext v
  simp only [Pi.smul_apply, Pi.zero_apply, valF]
  exact (Submodule.mem_torsionBy_iff (p : k) _).mp (e v).2

lemma LCF_valF_iff {n : ℕ} (e : (Fin n → G) → repTorsionP p E) : LCF r S (valF E p e) ↔ LCF r S e := by
  constructor
  · rintro ⟨F, hF, h⟩
    exact ⟨F, hF, fun g s hs => Subtype.ext (h g s hs)⟩
  · intro h
    exact h.comp _

variable {r S E p}

theorem clauseC (hdiv : ∀ x : E, ∃ y : E, (p : k) • y = x) (c : ↥(levelCocyclesSr₂ r S E)) :
    ∃ b : (Fin 2 → G) → E, LCF r S b ∧ ∀ v : Fin 2 → G, (p : k) • b v = (c : G × G → E) (v 0, v 1) := by
  choose sec hsec using hdiv
  refine ⟨sec ∘ read₂ (c : G × G → E), ?_, fun v => hsec _⟩
  exact ((LCF_read₂_iff (c : G × G → E)).2 c.2.2).comp sec

theorem clauseA (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a))
    (hdiv : ∀ x : E, ∃ y : E, (p : k) • y = x)
    (c : ↥(levelCocyclesSr₂ r S E)) (b : (Fin 2 → G) → E) (hb : LCF r S b)
    (hpb : ∀ v : Fin 2 → G, (p : k) • b v = (c : G × G → E) (v 0, v 1)) :
    (∃ e : (Fin 2 → G) → repTorsionP p E, LCF r S e ∧
        ((inhomogeneousCochains E).d 2 3).hom b = ((inhomogeneousCochains E).d 2 3).hom (valF E p e)) ↔
      ∃ y : continuousH2Sr r S E, continuousH2Srπ r S E c = p • y := by
  constructor
  · rintro ⟨e, he, hde⟩

    have hw : unread₂ (b - valF E p e) ∈ levelCocyclesSr₂ r S E := by
      refine ⟨(d23_read₂_eq_zero_iff E _).1 ?_, LCF_unread₂ (hb.sub ((LCF_valF_iff r S E p e).2 he))⟩
      rw [read₂_unread₂, map_sub, hde, sub_self]
    refine ⟨continuousH2Srπ r S E ⟨_, hw⟩, ?_⟩
    have hc : c = (p : k) • (⟨_, hw⟩ : ↥(levelCocyclesSr₂ r S E)) := by
      apply Subtype.ext
      funext x
      change (c : G × G → E) x = (p : k) • ((b - valF E p e) ![x.1, x.2])
      rw [Pi.sub_apply, smul_sub, hpb]
      have h0 : (p : k) • valF E p e ![x.1, x.2] = 0 := by
        have := congrFun (p_smul_valF E p e) ![x.1, x.2]
        simpa using this
      rw [h0, sub_zero]
      rfl
    rw [hc, map_smul, Nat.cast_smul_eq_nsmul]
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y

    have h0 : continuousH2Srπ r S E (c - (p : k) • z) = 0 := by
      rw [map_sub, map_smul, Nat.cast_smul_eq_nsmul, hy, sub_self]
    rw [continuousH2Srπ_eq_zero_iff, mem_levelCoboundariesSr₂_iff] at h0
    obtain ⟨a, ha, hda⟩ := h0
    obtain ⟨a', ha', hpa'⟩ := exists_lift r S E p hdiv ha
    have hpa'' : (p : k) • a' = a := funext hpa'

    set e' : (Fin 2 → G) → E := b - read₂ (z : G × G → E) - ((inhomogeneousCochains E).d 1 2).hom (read₁ a') with he'
    have hpe' : ∀ v, (p : k) • e' v = 0 := by
      intro v
      have h1 : (p : k) • ((inhomogeneousCochains E).d 1 2).hom (read₁ a') = read₂ ((d₁₂ E).hom a) := by
        rw [← map_smul, show (p : k) • read₁ a' = read₁ ((p : k) • a') from rfl, hpa'', d12_read₁]
      have h2 := congrFun h1 v
      simp only [Pi.smul_apply] at h2
      rw [he', Pi.sub_apply, Pi.sub_apply, smul_sub, smul_sub, hpb, h2, hda]
      simp [read₂, Pi.sub_apply, Pi.smul_apply]
    refine ⟨fun v => ⟨e' v, (Submodule.mem_torsionBy_iff (p : k) _).2 (hpe' v)⟩, ?_, ?_⟩
    · rw [← LCF_valF_iff]
      change LCF r S e'
      rw [he']
      refine (hb.sub ((LCF_read₂_iff _).2 z.2.2)).sub ?_
      rw [d12_read₁, LCF_read₂_iff]
      exact isLevelConstantSr₂_d₁₂ r S E hsm ha'
    · change _ = ((inhomogeneousCochains E).d 2 3).hom e'
      rw [he', map_sub, map_sub, d23_d12, sub_zero, (d23_read₂_eq_zero_iff E _).2 z.2.1, sub_zero]

theorem clauseB (u : (Fin 3 → G) → repTorsionP p E) :
    (∃ w : (Fin 2 → G) → E, LCF r S w ∧ ((inhomogeneousCochains E).d 2 3).hom w = valF E p u) ↔
      ∃ (c : ↥(levelCocyclesSr₂ r S E)) (b : (Fin 2 → G) → E) (e : (Fin 2 → G) → repTorsionP p E),
        LCF r S b ∧ LCF r S e ∧ (∀ v : Fin 2 → G, (p : k) • b v = (c : G × G → E) (v 0, v 1)) ∧
        valF E p u = ((inhomogeneousCochains E).d 2 3).hom b + ((inhomogeneousCochains E).d 2 3).hom (valF E p e) := by
  constructor
  · rintro ⟨w, hw, hdw⟩
    have hc : unread₂ ((p : k) • w) ∈ levelCocyclesSr₂ r S E := by
      refine ⟨(d23_read₂_eq_zero_iff E _).1 ?_, LCF_unread₂ (hw.comp _)⟩
      rw [read₂_unread₂, map_smul, hdw, p_smul_valF]
    refine ⟨⟨_, hc⟩, w, 0, hw, LCF_zero, fun v => ?_, ?_⟩
    · change (p : k) • w v = ((p : k) • w) ![v 0, v 1]
      rw [Pi.smul_apply]
      congr 2
      funext i; fin_cases i <;> rfl
    · rw [← hdw]
      have : valF E p (0 : (Fin 2 → G) → repTorsionP p E) = 0 := rfl
      rw [this, map_zero, add_zero]
  · rintro ⟨c, b, e, hb, he, -, hu⟩
    exact ⟨b + valF E p e, hb.add ((LCF_valF_iff r S E p e).2 he), by rw [map_add, hu]⟩

end clauses

end CycBaseLES3

end

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) {G : Type} [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (E : Rep.{0} ℤ G)
    (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a))
    (hdiv : ∀ x : E, ∃ y : E, (p : ℤ) • y = x) :
    (∀ c : ↥(levelCocyclesSr₂ r S E), ∃ b : (Fin 2 → G) → E,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → b (g * s) = b g) ∧
      ∀ v : Fin 2 → G, (p : ℤ) • b v = (c : G × G → E) (v 0, v 1)) ∧
    (∀ (c : ↥(levelCocyclesSr₂ r S E)) (b : (Fin 2 → G) → E),
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → b (g * s) = b g) →
      (∀ v : Fin 2 → G, (p : ℤ) • b v = (c : G × G → E) (v 0, v 1)) →
      ((∃ e : (Fin 2 → G) → repTorsionP p E,
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
            ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → e (g * s) = e g) ∧
          ((inhomogeneousCochains E).d 2 3).hom b = ((inhomogeneousCochains E).d 2 3).hom (fun v => ((e v : repTorsionP p E) : E))) ↔
        ∃ y : continuousH2Sr r S E, continuousH2Srπ r S E c = p • y)) ∧
    (∀ u : (Fin 3 → G) → repTorsionP p E,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 3 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → u (g * s) = u g) →
      ((inhomogeneousCochains (repTorsionP p E)).d 3 4).hom u = 0 →
      ((∃ w : (Fin 2 → G) → E,
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
            ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
          ((inhomogeneousCochains E).d 2 3).hom w = fun t => ((u t : repTorsionP p E) : E)) ↔
        ∃ (c : ↥(levelCocyclesSr₂ r S E)) (b : (Fin 2 → G) → E) (e : (Fin 2 → G) → repTorsionP p E),
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
            ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → b (g * s) = b g ∧ e (g * s) = e g) ∧
          (∀ v : Fin 2 → G, (p : ℤ) • b v = (c : G × G → E) (v 0, v 1)) ∧
          (fun t => ((u t : repTorsionP p E) : E)) =
            ((inhomogeneousCochains E).d 2 3).hom b + ((inhomogeneousCochains E).d 2 3).hom (fun v => ((e v : repTorsionP p E) : E)))) := by
  have hdiv' := hdiv
  simp only [← int_smul_eq_zsmul E.hV2] at hdiv'
  refine ⟨fun c => ?_, fun c b hb hpb => ?_, fun u _ _ => ?_⟩
  · have h := CycBaseLES3.clauseC (r := r) (S := S) (E := E) (p := p) hdiv' c
    simp only [← int_smul_eq_zsmul E.hV2]
    exact h
  · have hpb' := hpb
    simp only [← int_smul_eq_zsmul E.hV2] at hpb'
    have h := CycBaseLES3.clauseA (r := r) (S := S) (E := E) (p := p) hsm hdiv' c b hb hpb'
    exact h
  · have h := CycBaseLES3.clauseB (r := r) (S := S) (E := E) (p := p) u
    simp only [← int_smul_eq_zsmul E.hV2]
    refine h.trans ⟨?_, ?_⟩
    · rintro ⟨c, b, e, hb, he, h1, h2⟩
      exact ⟨c, b, e, CycBaseLES3.LCF_and hb he, h1, h2⟩
    · rintro ⟨c, b, e, ⟨F, hF, h⟩, h1, h2⟩
      exact ⟨c, b, e, ⟨F, hF, fun g s hs => (h g s hs).1⟩, ⟨F, hF, fun g s hs => (h g s hs).2⟩, h1, h2⟩

end S_groupCohomology_kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible
end P2MW
export P2MW.S_groupCohomology_kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible (solution)
