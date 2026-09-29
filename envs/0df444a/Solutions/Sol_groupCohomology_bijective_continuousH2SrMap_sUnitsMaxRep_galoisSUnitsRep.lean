-- Prove2me | solution 1 for groupCohomology.bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/784ea590-1582-5931-8ad3-41bd45f73fd2

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_GroupCohomology_GaloisSUnits
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_GroupCohomology_LevelSubgroup
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory groupCohomology ValuationSubring NumberField.LevelArith

noncomputable section

local instance isAlgebraicQbar_br : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_br : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_br : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
local instance isGaloisQbar_br : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

namespace P2MBridge

local notation "ℚb" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (S : Finset Nat.Primes) (L : IntermediateField ℚ ℚb)

set_option hygiene false in
local notation "U" => IntermediateField.fixingSubgroup L

abbrev SUn : Rep ℤ ↥U := Rep.res (U).subtype (galoisSUnitsRep S)

abbrev ES : Rep ℤ ↥U := sUnitsMaxRep S L

abbrev SU : Type := Additive ↥(galoisSUnits S)

private def _root_.P2MBridge.val (x : SU S) : ℚbˣ := ((Additive.toMul x : ↥(galoisSUnits S)) : ℚbˣ)

p2m_export "P2MBridge" "val"
lemma val_injective : Function.Injective (val S) := fun _ _ h => Additive.toMul.injective (Subtype.ext h)
lemma val_add (x y : SU S) : val S (x + y) = val S x * val S y := rfl
lemma val_sub (x y : SU S) : val S (x - y) = val S x / val S y := by
  simp only [val, toMul_sub, Subgroup.coe_div]
lemma val_zero : val S 0 = 1 := rfl

def act (g : ↥U) (x : SU S) : SU S := Additive.ofMul ((g : Γ) • Additive.toMul x)

lemma act_eq (g : ↥U) (x : SU S) : (SUn S L).ρ g x = act S L g x := rfl
lemma val_act (g : ↥U) (x : SU S) : val S (act S L g x) = (g : Γ) • val S x := rfl
lemma act_eq_self_of_smul_eq {g : ↥U} {x : SU S} (h : (g : Γ) • val S x = val S x) : act S L g x = x :=
  val_injective S ((val_act S L g x).trans h)

def dU₁ (Y : ↥U → SU S) : ↥U × ↥U → SU S := (d₁₂ (SUn S L)).hom Y

lemma dU₁_apply (Y : ↥U → SU S) (g h : ↥U) : dU₁ S L Y (g, h) = act S L g (Y h) - Y (g * h) + Y g :=
  d₁₂_hom_apply (SUn S L) Y (g, h)

def valE (x : ES S L) : ℚbˣ := sUnitsMaxRep.val S L x

lemma valE_injective : Function.Injective (valE S L) := fun _ _ h => Subtype.ext (Additive.toMul.injective h)
lemma valE_add (x y : ES S L) : valE S L (x + y) = valE S L x * valE S L y := rfl
lemma valE_sub (x y : ES S L) : valE S L (x - y) = valE S L x / valE S L y := rfl
lemma valE_ρ (g : ↥U) (x : ES S L) : valE S L ((ES S L).ρ g x) = (g : Γ) • valE S L x := rfl

def dE₁ (Y : ↥U → ES S L) : ↥U × ↥U → ES S L := (d₁₂ (ES S L)).hom Y

lemma dE₁_apply (Y : ↥U → ES S L) (g h : ↥U) : dE₁ S L Y (g, h) = (ES S L).ρ g (Y h) - Y (g * h) + Y g :=
  d₁₂_hom_apply (ES S L) Y (g, h)

lemma exists_normal_level (F' : IntermediateField ℚ ℚb) (hF' : F'.IsUnramifiedOutside S) :
    ∃ F'' : IntermediateField ℚ ℚb, F''.IsUnramifiedOutside S ∧ F''.fixingSubgroup.Normal ∧ F' ≤ F'' := by
  haveI := hF'.1
  haveI : Normal ℚ (IntermediateField.normalClosure ℚ F' ℚb) := by
    have := normalClosure.normal ℚ (↥F') ℚb; convert this <;> first | rfl | exact Subsingleton.elim _ _
  refine ⟨IntermediateField.normalClosure ℚ F' ℚb, hF'.normalClosure, ?_, IntermediateField.le_normalClosure F'⟩
  have := groupCohomology.normal_comap_fixingSubgroup (MonoidHom.id Γ) (IntermediateField.normalClosure ℚ F' ℚb)
  rwa [Subgroup.comap_id] at this

lemma mem_of_forall_smul_eq {F₀ : IntermediateField ℚ ℚb} {x : ℚb} (h : ∀ σ ∈ F₀.fixingSubgroup, σ x = x) : x ∈ F₀ := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup F₀]
  exact (IntermediateField.mem_fixedField_iff _ _).2 h

lemma not_liesOverPrime_of_liesOverPrime (A : ValuationSubring ℚb) {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime) (hne : q ≠ q')
    (h : A.LiesOverPrime q) : ¬ A.LiesOverPrime q' := by
  intro h'
  rw [LiesOverPrime, ValuationSubring.mem_nonunits_iff] at h h'
  have hcop : Nat.Coprime q q' := (Nat.coprime_primes hq hq').2 hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hint : ∀ z : ℤ, A.valuation (z : ℚb) ≤ 1 := fun z => (A.valuation_le_one_iff _).2 (by simp)
  have h1 : A.valuation ((a : ℚb) * q + (b : ℚb) * q') < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [Valuation.map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hint a) zero_le' h
    · rw [Valuation.map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hint b) zero_le' h'
  have h2 : ((a : ℚb) * q + (b : ℚb) * q') = 1 := by exact_mod_cast hab
  rw [h2, Valuation.map_one] at h1
  exact lt_irrefl _ h1

lemma mem_sUnitsMax {x : ℚbˣ} (hx : x ∈ galoisSUnits S) {F₀ : IntermediateField ℚ ℚb} (hF₀ : F₀.IsUnramifiedOutside S)
    (hxF : (x : ℚb) ∈ F₀) : x ∈ sUnitsMax S := by
  refine ⟨⟨F₀, hF₀, hxF⟩, fun q hq A hA => ?_⟩
  refine hx A fun q' hq' h' => ?_
  have hne : (q : ℕ) ≠ (q' : ℕ) := fun e => hq (by rwa [show q = q' from Subtype.ext e])
  exact not_liesOverPrime_of_liesOverPrime A q.2 q'.2 hne hA h'

variable {S L} in

lemma mem_sUnitsMaxStable {x : ℚbˣ} (hx : x ∈ galoisSUnits S) {F'' : IntermediateField ℚ ℚb} (hF'' : F''.IsUnramifiedOutside S)
    (hN : F''.fixingSubgroup.Normal) (hfix : ∀ σ ∈ F''.fixingSubgroup, σ • x = x) : x ∈ sUnitsMaxStable S L := by
  rw [mem_sUnitsMaxStable_iff]
  intro γ
  refine mem_sUnitsMax S (smul_mem_galoisSUnits _ hx) hF'' (mem_of_forall_smul_eq fun σ hσ => ?_)
  have hc : (γ : Γ)⁻¹ * σ * (γ : Γ) ∈ F''.fixingSubgroup := by
    have := hN.conj_mem σ hσ (γ : Γ)⁻¹; simpa using this
  have e : σ • ((γ : Γ) • x) = (γ : Γ) • x := by
    have := hfix _ hc
    calc σ • ((γ : Γ) • x) = (γ : Γ) • (((γ : Γ)⁻¹ * σ * (γ : Γ)) • x) := by simp only [mul_smul, smul_inv_smul]
      _ = (γ : Γ) • x := by rw [this]
  have := congrArg (fun u : ℚbˣ => (u : ℚb)) e
  simpa [AlgEquiv.smul_units_def, Units.coe_map] using this

variable {S L} in

lemma smul_val_eq_of_cocycle {f : ↥U × ↥U → SU S} (hf : f ∈ cocycles₂ (SUn S L)) {F'' : IntermediateField ℚ ℚb}
    (hFU : F''.fixingSubgroup ≤ U) (hN : F''.fixingSubgroup.Normal)
    (hc : ∀ g g' s s' : ↥U, (s : Γ) ∈ F''.fixingSubgroup → (s' : Γ) ∈ F''.fixingSubgroup → f (g * s, g' * s') = f (g, g'))
    (h k : ↥U) {σ : Γ} (hσ : σ ∈ F''.fixingSubgroup) : σ • val S (f (h, k)) = val S (f (h, k)) := by
  let u : ↥U := ⟨σ, hFU hσ⟩
  have hu : (u : Γ) ∈ F''.fixingSubgroup := hσ
  have hcoc := (mem_cocycles₂_iff (A := SUn S L) f).1 hf

  have e1 := hcoc u h k
  have e0 := hcoc 1 h k
  have hconj : ((h⁻¹ * u * h : ↥U) : Γ) ∈ F''.fixingSubgroup := hN.conj_mem' σ hσ (h : Γ)
  have h1 : f (u * h, k) = f (h, k) := by
    have e : u * h = h * (h⁻¹ * u * h) := by group
    rw [e]
    have := hc h k (h⁻¹ * u * h) 1 hconj (Subgroup.one_mem _)
    rwa [mul_one] at this
  have h2 : f (u, h * k) = f (1, h * k) := by
    have := hc 1 (h * k) u 1 hu (Subgroup.one_mem _); rwa [one_mul, mul_one] at this
  have h3 : f (u, h) = f (1, h) := by
    have := hc 1 h u 1 hu (Subgroup.one_mem _); rwa [one_mul, mul_one] at this
  rw [h1, h3, h2] at e1
  rw [one_mul, map_one, Module.End.one_apply] at e0

  have e2 : (SUn S L).ρ u (f (h, k)) = f (h, k) := add_right_cancel (e1.symm.trans e0)
  have := congrArg (val S) e2
  rwa [act_eq, val_act] at this

variable {S L} in

lemma smul_val_eq_of_dU₁ {Y : ↥U → SU S} {F₀ : IntermediateField ℚ ℚb} (hFU : F₀.fixingSubgroup ≤ U)
    (hN : F₀.fixingSubgroup.Normal)
    (hc : ∀ g s : ↥U, (s : Γ) ∈ F₀.fixingSubgroup → Y (g * s) = Y g)
    (hd : ∀ g h s : ↥U, (s : Γ) ∈ F₀.fixingSubgroup → dU₁ S L Y (g * s, h) = dU₁ S L Y (g, h))
    (h : ↥U) {σ : Γ} (hσ : σ ∈ F₀.fixingSubgroup) : σ • val S (Y h) = val S (Y h) := by
  let s : ↥U := ⟨σ, hFU hσ⟩
  have hs : (s : Γ) ∈ F₀.fixingSubgroup := hσ
  have e := hd 1 h s hs
  have e1 : Y s = Y 1 := by have := hc 1 s hs; rwa [one_mul] at this
  rw [dU₁_apply, dU₁_apply, one_mul, one_mul, e1] at e
  have e2 : Y (s * h) = Y h := by
    have : s * h = h * (h⁻¹ * s * h) := by group
    rw [this]; exact hc _ _ (hN.conj_mem' σ hσ (h : Γ))
  rw [e2, add_left_inj, sub_left_inj] at e
  have e3 : act S L s (Y h) = Y h := by
    rw [e]; apply act_eq_self_of_smul_eq; rw [Subgroup.coe_one, one_smul]
  have := congrArg (val S) e3
  rwa [val_act] at this

variable (hL : L.IsUnramifiedOutside S)
  (φ : sUnitsMaxRep S L →ₗ[ℤ] Rep.res (U).subtype (galoisSUnitsRep S))
  (hφv : ∀ x : sUnitsMaxRep S L, ((Additive.toMul (φ x) : ↥(galoisSUnits S)) : ℚbˣ) = sUnitsMaxRep.val S L x)
  (hφ : ∀ (g : ↥U) (a : sUnitsMaxRep S L), φ ((sUnitsMaxRep S L).ρ g a) = (Rep.res (U).subtype (galoisSUnitsRep S)).ρ g (φ a))

include hφv in
lemma val_φ (x : ES S L) : val S (φ x) = valE S L x := hφv x

include hφv in
lemma φ_injective : Function.Injective φ := fun x y h => valE_injective S L (by rw [← val_φ S L φ hφv, ← val_φ S L φ hφv, h])

def liftE (x : SU S) (hx : val S x ∈ sUnitsMaxStable S L) : ES S L := ⟨Additive.ofMul (val S x), hx⟩

lemma valE_liftE (x : SU S) (hx : val S x ∈ sUnitsMaxStable S L) : valE S L (liftE S L x hx) = val S x := rfl

include hφv in
lemma φ_liftE (x : SU S) (hx : val S x ∈ sUnitsMaxStable S L) : φ (liftE S L x hx) = x :=
  val_injective S (by rw [val_φ S L φ hφv, valE_liftE])

include hL hφv hφ in

lemma exists_lift_cocycle (f : ↥U × ↥U → SU S) (hf : f ∈ levelCocyclesSr₂ (U).subtype S (SUn S L)) :
    ∃ ft : ↥U × ↥U → ES S L, ft ∈ levelCocyclesSr₂ (U).subtype S (ES S L) ∧ ∀ g, φ (ft g) = f g := by
  obtain ⟨hfc, F', hF', hcst⟩ := (mem_levelCocyclesSr₂_iff _ _ _ _).1 hf
  obtain ⟨F'', hF'', hN, hle⟩ := exists_normal_level S (F' ⊔ L) (hF'.sup hL)
  have hFU : F''.fixingSubgroup ≤ U := IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hle)
  have hF''F' : F''.fixingSubgroup ≤ F'.fixingSubgroup := IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hle)
  have hc'' : ∀ g g' s s' : ↥U, (s : Γ) ∈ F''.fixingSubgroup → (s' : Γ) ∈ F''.fixingSubgroup → f (g * s, g' * s') = f (g, g') :=
    fun g g' s s' hs hs' => hcst g g' s s' (hF''F' hs) (hF''F' hs')
  have hval : ∀ h k, val S (f (h, k)) ∈ sUnitsMaxStable S L := fun h k =>
    mem_sUnitsMaxStable (Additive.toMul (f (h, k))).2 hF'' hN (fun σ hσ => smul_val_eq_of_cocycle hfc hFU hN hc'' h k hσ)
  refine ⟨fun g => liftE S L (f g) (hval g.1 g.2), ?_, fun g => φ_liftE S L φ hφv _ _⟩
  refine (mem_levelCocyclesSr₂_iff _ _ _ _).2 ⟨?_, F', hF', fun g g' s s' hs hs' => ?_⟩
  ·
    rw [mem_cocycles₂_iff (A := ES S L)]
    intro g h j
    apply φ_injective S L φ hφv
    rw [map_add, map_add, hφ, φ_liftE S L φ hφv, φ_liftE S L φ hφv, φ_liftE S L φ hφv, φ_liftE S L φ hφv]
    exact (mem_cocycles₂_iff (A := SUn S L) f).1 hfc g h j
  · exact valE_injective S L (by simp only [valE_liftE]; rw [hcst g g' s s' hs hs'])

include hL hφv hφ in

lemma lift_coboundary (ft : ↥U × ↥U → ES S L) (hft : ft ∈ levelCocyclesSr₂ (U).subtype S (ES S L))
    (h0 : (fun g => φ (ft g)) ∈ levelCoboundariesSr₂ (U).subtype S (SUn S L)) :
    ft ∈ levelCoboundariesSr₂ (U).subtype S (ES S L) := by
  obtain ⟨Y, ⟨F₁, hF₁, hYc⟩, hYd⟩ := (mem_levelCoboundariesSr₂_iff _ _ _ _).1 h0
  change ↥U → SU S at Y
  change dU₁ S L Y = fun g => φ (ft g) at hYd
  obtain ⟨-, F', hF', hcst⟩ := (mem_levelCocyclesSr₂_iff _ _ _ _).1 hft
  obtain ⟨F₀, hF₀, hN, hle⟩ := exists_normal_level S (F₁ ⊔ F' ⊔ L) ((hF₁.sup hF').sup hL)
  have hFU : F₀.fixingSubgroup ≤ U := IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hle)
  have h₀₁ : F₀.fixingSubgroup ≤ F₁.fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone ((le_sup_left.trans le_sup_left).trans hle)
  have h₀' : F₀.fixingSubgroup ≤ F'.fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone ((le_sup_right.trans le_sup_left).trans hle)
  have hc : ∀ g s : ↥U, (s : Γ) ∈ F₀.fixingSubgroup → Y (g * s) = Y g := fun g s hs => hYc g s (h₀₁ hs)
  have hd : ∀ g h s : ↥U, (s : Γ) ∈ F₀.fixingSubgroup → dU₁ S L Y (g * s, h) = dU₁ S L Y (g, h) := by
    intro g h s hs
    rw [hYd]
    change φ (ft (g * s, h)) = φ (ft (g, h))
    have := hcst g h s 1 (h₀' hs) (Subgroup.one_mem _)
    rw [mul_one] at this
    rw [this]
  have hval : ∀ h, val S (Y h) ∈ sUnitsMaxStable S L := fun h =>
    mem_sUnitsMaxStable (Additive.toMul (Y h)).2 hF₀ hN (fun σ hσ => smul_val_eq_of_dU₁ hFU hN hc hd h hσ)
  refine (mem_levelCoboundariesSr₂_iff _ _ _ _).2 ⟨fun h => liftE S L (Y h) (hval h), ⟨F₁, hF₁, fun g s hs => ?_⟩, ?_⟩
  · exact valE_injective S L (by simp only [valE_liftE]; rw [hYc g s hs])
  · funext g
    apply φ_injective S L φ hφv
    change φ (dE₁ S L (fun h => liftE S L (Y h) (hval h)) (g.1, g.2)) = φ (ft g)
    rw [dE₁_apply, map_add, map_sub, hφ, φ_liftE S L φ hφv, φ_liftE S L φ hφv, φ_liftE S L φ hφv]
    have := congr_fun hYd (g.1, g.2)
    rw [dU₁_apply] at this
    exact this

include hL hφv in
theorem main :
    Function.Bijective
      (continuousH2SrMap (rH := (U).subtype) (rG := (U).subtype) (A := sUnitsMaxRep S L) (B := Rep.res (U).subtype (galoisSUnitsRep S))
        (MonoidHom.id ↥U) (fun _ => rfl) S φ hφ) := by
  constructor
  ·
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨ft, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [Submodule.mkQ_apply, ← Submodule.mkQ_apply, continuousH2SrMap_continuousH2Srπ, continuousH2Srπ_eq_zero_iff] at hx
    rw [Submodule.mkQ_apply, ← Submodule.mkQ_apply (p := (levelCoboundariesSr₂ (U).subtype S (ES S L)).comap _),
      continuousH2Srπ_eq_zero_iff]
    exact lift_coboundary S L hL φ hφv hφ ft.1 ft.2 hx
  ·
    intro y
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨ft, hft, hφft⟩ := exists_lift_cocycle S L hL φ hφv hφ f.1 f.2
    refine ⟨continuousH2Srπ _ _ _ ⟨ft, hft⟩, ?_⟩
    rw [continuousH2SrMap_continuousH2Srπ]
    congr 1
    exact Subtype.ext (funext hφft)

end P2MBridge

end

open NumberField.LevelArith in
theorem solution
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
    (φ : sUnitsMaxRep S L →ₗ[ℤ] Rep.res L.fixingSubgroup.subtype (galoisSUnitsRep S))
    (hφv : ∀ x : sUnitsMaxRep S L,
      ((Additive.toMul (φ x) : ↥(galoisSUnits S)) : (AlgebraicClosure ℚ)ˣ) = sUnitsMaxRep.val S L x)
    (hφ : ∀ (g : ↥L.fixingSubgroup) (a : sUnitsMaxRep S L),
      φ ((sUnitsMaxRep S L).ρ g a) = (Rep.res L.fixingSubgroup.subtype (galoisSUnitsRep S)).ρ g (φ a)) :
    Function.Bijective
      (continuousH2SrMap (rH := L.fixingSubgroup.subtype) (rG := L.fixingSubgroup.subtype)
        (A := sUnitsMaxRep S L) (B := Rep.res L.fixingSubgroup.subtype (galoisSUnitsRep S))
        (MonoidHom.id ↥L.fixingSubgroup) (fun _ => rfl) S φ hφ) :=
  P2MBridge.main S L hL φ hφv hφ

end S_groupCohomology_bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep
end P2MW
export P2MW.S_groupCohomology_bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep (solution)
