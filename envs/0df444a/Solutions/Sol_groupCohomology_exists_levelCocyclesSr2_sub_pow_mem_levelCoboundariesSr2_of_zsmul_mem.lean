-- Prove2me | solution 1 for groupCohomology.exists_levelCocyclesSr2_sub_pow_mem_levelCoboundariesSr2_of_zsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/4e729ea9-eed2-58dc-a3bb-4a9a01a666d2

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_GaloisSUnits
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_sup_adjoin_simple_of_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_levelCocyclesSr2_sub_pow_mem_levelCoboundariesSr2_of_zsmul_mem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory groupCohomology ValuationSubring

noncomputable section

local instance isAlgebraicQbar_kg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_kg : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_kg : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
local instance isGaloisQbar_kg : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

namespace P2MKglob

local notation "ℚb" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (p : ℕ) [hp : Fact p.Prime] (S : Finset Nat.Primes) (U : Subgroup Γ) (ζ : ℚbˣ) (hζ : IsPrimitiveRoot ζ p)
  (hζS : ζ ∈ galoisSUnits S) (hU : ∀ σ ∈ U, σ • ζ = ζ)

abbrev SUn : Rep ℤ ↥U := Rep.res U.subtype (galoisSUnitsRep S)

abbrev Tr : Rep (ZMod p) ↥U := Rep.trivial (ZMod p) ↥U (ZMod p)

abbrev SU : Type := Additive ↥(galoisSUnits S)

private def _root_.P2MKglob.val (x : SU S) : ℚbˣ := ((Additive.toMul x : ↥(galoisSUnits S)) : ℚbˣ)

p2m_export "P2MKglob" "val"
private lemma _root_.P2MKglob.val_injective : Function.Injective (val S) := fun _ _ h => Additive.toMul.injective (Subtype.ext h)

p2m_export "P2MKglob" "val_injective"
private lemma _root_.P2MKglob.val_add (x y : SU S) : val S (x + y) = val S x * val S y := rfl
p2m_export "P2MKglob" "val_add"
lemma val_sub (x y : SU S) : val S (x - y) = val S x / val S y := by
  simp only [val, toMul_sub, Subgroup.coe_div]
lemma val_zsmul (n : ℤ) (x : SU S) : val S (n • x) = val S x ^ n := by
  simp only [val, toMul_zsmul, Subgroup.coe_zpow]
lemma val_zero : val S 0 = 1 := rfl

def act (g : ↥U) (x : SU S) : SU S := Additive.ofMul ((g : Γ) • Additive.toMul x)

lemma act_eq (g : ↥U) (x : SU S) : (SUn S U).ρ g x = act S U g x := rfl

lemma act_mul (g h : ↥U) (x : SU S) : act S U (g * h) x = act S U g (act S U h x) := by
  simp only [act, toMul_ofMul, Subgroup.coe_mul, mul_smul]

lemma val_act (g : ↥U) (x : SU S) : val S (act S U g x) = (g : Γ) • val S x := rfl

lemma act_eq_self_of_smul_eq {g : ↥U} {x : SU S} (h : (g : Γ) • val S x = val S x) : act S U g x = x :=
  val_injective S ((val_act S U g x).trans h)

def dU₁ (Y : ↥U → SU S) : ↥U × ↥U → SU S := (d₁₂ (SUn S U)).hom Y

lemma dU₁_apply (Y : ↥U → SU S) (g h : ↥U) : dU₁ S U Y (g, h) = act S U g (Y h) - Y (g * h) + Y g :=
  d₁₂_hom_apply (SUn S U) Y (g, h)

lemma dU₁_zsmul (n : ℤ) (Y : ↥U → SU S) : dU₁ S U (n • Y) = n • dU₁ S U Y := map_zsmul (d₁₂ (SUn S U)).hom n Y

lemma dU₁_mem_cocycles₂ (Y : ↥U → SU S) : dU₁ S U Y ∈ cocycles₂ (SUn S U) := d₁₂_apply_mem_cocycles₂ (A := SUn S U) Y

include hζ in
lemma zeta_pow_mod (m : ℕ) : ζ ^ (m % p) = ζ ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

def chi : ZMod p →+ SU S :=
  AddMonoidHom.mk' (fun n => Additive.ofMul (⟨ζ ^ n.val, Subgroup.pow_mem _ hζS _⟩ : ↥(galoisSUnits S))) fun a b => by
    change Additive.ofMul _ = Additive.ofMul _ + Additive.ofMul _
    rw [← ofMul_mul]
    congr 1
    apply Subtype.ext
    change ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val
    rw [← pow_add, ZMod.val_add, zeta_pow_mod p ζ hζ]

lemma chi_apply (n : ZMod p) : chi p S ζ hζ hζS n = Additive.ofMul (⟨ζ ^ n.val, Subgroup.pow_mem _ hζS _⟩ : ↥(galoisSUnits S)) := rfl

lemma val_chi (n : ZMod p) : val S (chi p S ζ hζ hζS n) = ζ ^ n.val := rfl

lemma chi_injective : Function.Injective (chi p S ζ hζ hζS) := by
  intro a b h
  have h' : ζ ^ a.val = ζ ^ b.val := by rw [← val_chi p S ζ hζ hζS, ← val_chi p S ζ hζ hζS, h]
  exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h')

include hU in
lemma act_chi (g : ↥U) (n : ZMod p) : act S U g (chi p S ζ hζ hζS n) = chi p S ζ hζ hζS n := by
  apply act_eq_self_of_smul_eq
  rw [val_chi, smul_pow', hU _ g.2]

include hζ in
lemma zeta_val : IsPrimitiveRoot ((ζ : ℚbˣ) : ℚb) p := hζ.map_of_injective Units.coeHom_injective

lemma exists_chi_eq {x : SU S} (hx : (p : ℤ) • x = 0) : ∃ n : ZMod p, chi p S ζ hζ hζS n = x := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hx' : ((val S x : ℚbˣ) : ℚb) ^ p = 1 := by
    have := congrArg (fun y => ((val S y : ℚbˣ) : ℚb)) hx
    simp only [val_zsmul, zpow_natCast, val_zero, Units.val_pow_eq_pow_val, Units.val_one] at this
    exact this
  obtain ⟨i, hi, hζi⟩ := (zeta_val p ζ hζ).eq_pow_of_pow_eq_one hx'
  refine ⟨(i : ZMod p), val_injective S (Units.ext ?_)⟩
  rw [val_chi, ZMod.val_natCast, Nat.mod_eq_of_lt hi, Units.val_pow_eq_pow_val, hζi]

def expo (z : ↥U × ↥U → ZMod p) : ↥U × ↥U → SU S := chi p S ζ hζ hζS ∘ z

lemma expo_eq (z : ↥U × ↥U → ZMod p) :
    expo p S U ζ hζ hζS z = fun g => Additive.ofMul (⟨ζ ^ (z g).val, Subgroup.pow_mem _ hζS _⟩ : ↥(galoisSUnits S)) := rfl

include hU in
lemma expo_mem_cocycles₂_iff (z : ↥U × ↥U → ZMod p) : expo p S U ζ hζ hζS z ∈ cocycles₂ (SUn S U) ↔ z ∈ cocycles₂ (Tr p U) := by
  refine (mem_cocycles₂_iff (A := SUn S U) (expo p S U ζ hζ hζS z)).trans ?_
  refine Iff.trans ?_ (mem_cocycles₂_iff (A := Tr p U) z).symm
  simp only [Rep.trivial_ρ_apply, Representation.trivial_apply]
  constructor
  · intro h g i j
    have h' := h g i j
    simp only [expo, Function.comp_apply] at h'
    rw [act_eq, act_chi p S U ζ hζ hζS hU] at h'
    apply chi_injective p S ζ hζ hζS
    rw [map_add, map_add]; exact h'
  · intro h g i j
    simp only [expo, Function.comp_apply]
    rw [act_eq, act_chi p S U ζ hζ hζS hU]
    have := congrArg (chi p S ζ hζ hζS) (h g i j)
    rw [map_add, map_add] at this
    exact this

lemma exists_normal_level (F' : IntermediateField ℚ ℚb) (hF' : F'.IsUnramifiedOutside S) :
    ∃ F'' : IntermediateField ℚ ℚb, F''.IsUnramifiedOutside S ∧ (F''.fixingSubgroup.comap U.subtype).Normal ∧
      (F''.fixingSubgroup.comap U.subtype).FiniteIndex ∧ F' ≤ F'' := by
  haveI := hF'.1
  haveI : Normal ℚ (IntermediateField.normalClosure ℚ F' ℚb) := by
    have := normalClosure.normal ℚ (↥F') ℚb; convert this <;> first | rfl | exact Subsingleton.elim _ _
  haveI : FiniteDimensional ℚ (IntermediateField.normalClosure ℚ F' ℚb) := hF'.normalClosure.1
  exact ⟨IntermediateField.normalClosure ℚ F' ℚb, hF'.normalClosure, inferInstance, inferInstance,
    IntermediateField.le_normalClosure F'⟩

lemma isUnramifiedOutside_finset_sup {ι : Type} (T : Finset ι) (E : ι → IntermediateField ℚ ℚb)
    (h : ∀ i, (E i).IsUnramifiedOutside S) : (T.sup E).IsUnramifiedOutside S := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sup_empty]; exact IntermediateField.isUnramifiedOutside_bot S
  | insert a T ha ih => rw [Finset.sup_insert]; exact (h a).sup ih

lemma exists_finset_of_isLevelConstantSr₁ {X : Type} {Y : ↥U → X} (hY : IsLevelConstantSr₁ U.subtype S Y)
    (E : IntermediateField ℚ ℚb) (hE : E.IsUnramifiedOutside S) :
    ∃ (F₀ : IntermediateField ℚ ℚb) (T : Finset ↥U), F₀.IsUnramifiedOutside S ∧ E ≤ F₀ ∧
      (F₀.fixingSubgroup.comap U.subtype).Normal ∧
      (∀ g s : ↥U, (s : Γ) ∈ F₀.fixingSubgroup → Y (g * s) = Y g) ∧
      ∀ g : ↥U, ∃ t ∈ T, Y g = Y t := by
  classical
  obtain ⟨F', hF', hc⟩ := hY
  obtain ⟨F₀, hF₀, hN, hFI, hle⟩ := exists_normal_level S U (F' ⊔ E) (hF'.sup hE)
  haveI := hFI
  let L₀ : Subgroup ↥U := F₀.fixingSubgroup.comap U.subtype
  haveI : Fintype (↥U ⧸ L₀) := Fintype.ofFinite _
  have hle' : F₀.fixingSubgroup ≤ F'.fixingSubgroup := IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hle)
  refine ⟨F₀, (Finset.univ : Finset (↥U ⧸ L₀)).image Quotient.out, hF₀, le_sup_right.trans hle, hN,
    fun g s hs => hc g s (hle' hs), fun g => ?_⟩
  refine ⟨(QuotientGroup.mk g : ↥U ⧸ L₀).out, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
  have h : ((QuotientGroup.mk g : ↥U ⧸ L₀).out : ↥U)⁻¹ * g ∈ L₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have : g = (QuotientGroup.mk g : ↥U ⧸ L₀).out * (((QuotientGroup.mk g : ↥U ⧸ L₀).out)⁻¹ * g) := by group
  conv_lhs => rw [this]
  exact hc _ _ (hle' h)

lemma mem_of_pow_mem (A : ValuationSubring ℚb) {r : ℚbˣ} (h1 : ((r ^ p : ℚbˣ) : ℚb) ∈ A) (h2 : (((r ^ p)⁻¹ : ℚbˣ) : ℚb) ∈ A) :
    (r : ℚb) ∈ A ∧ ((r⁻¹ : ℚbˣ) : ℚb) ∈ A := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hu1 : A.valuation ((r : ℚb) ^ p) ≤ 1 := (A.valuation_le_one_iff _).2 (by rwa [← Units.val_pow_eq_pow_val])
  have hu2 : A.valuation ((r : ℚb) ^ p)⁻¹ ≤ 1 := (A.valuation_le_one_iff _).2 (by rwa [← Units.val_pow_eq_pow_val, ← Units.val_inv_eq_inv_val])
  have hu0 : A.valuation ((r : ℚb) ^ p) ≠ 0 := by rw [Valuation.ne_zero_iff]; exact pow_ne_zero _ r.ne_zero
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 hu0)] at hu2
  have hu : A.valuation ((r : ℚb) ^ p) = 1 := le_antisymm hu1 hu2
  rw [map_pow] at hu
  have hv : A.valuation (r : ℚb) = 1 := by
    rcases lt_trichotomy (A.valuation (r : ℚb)) 1 with h | h | h
    · exact absurd hu (pow_lt_one₀ zero_le' h hp0).ne
    · exact h
    · exact absurd hu (one_lt_pow₀ h hp0).ne'
  refine ⟨(A.valuation_le_one_iff _).1 hv.le, (A.valuation_le_one_iff _).1 ?_⟩
  rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]

lemma root_mem {r : ℚbˣ} (h : r ^ p ∈ galoisSUnits S) : r ∈ galoisSUnits S := by
  intro A hA
  obtain ⟨h1, h2⟩ := h A hA
  exact mem_of_pow_mem p A h1 h2

lemma exists_pth_root (u : ℚbˣ) : ∃ r : ℚbˣ, r ^ p = u := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : ℚb) hp.out.pos
  have hz0 : z ≠ 0 := by
    intro h; rw [h, zero_pow hp.out.ne_zero] at hz; exact u.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩

def root (x : SU S) : SU S :=
  Additive.ofMul ⟨(exists_pth_root p (val S x)).choose,
    root_mem p S (by rw [(exists_pth_root p (val S x)).choose_spec]; exact (Additive.toMul x).2)⟩

lemma val_root_pow (x : SU S) : val S (root p S x) ^ p = val S x := (exists_pth_root p (val S x)).choose_spec

lemma p_zsmul_root (x : SU S) : (p : ℤ) • root p S x = x :=
  val_injective S (by rw [val_zsmul, zpow_natCast, val_root_pow])

lemma smul_eq_of_mem_fixingSubgroup {u : ℚbˣ} {σ : Γ}
    (hσ : σ ∈ (IntermediateField.adjoin ℚ {((u : ℚbˣ) : ℚb)}).fixingSubgroup) : σ • u = u := by
  ext
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (IntermediateField.mem_adjoin_simple_self ℚ _)

variable {S U} in

lemma smul_val_eq_of_dU₁ {Y : ↥U → SU S} {F₀ : IntermediateField ℚ ℚb} (hFU : F₀.fixingSubgroup ≤ U)
    (hN : (F₀.fixingSubgroup.comap U.subtype).Normal)
    (hc : ∀ g s : ↥U, (s : Γ) ∈ F₀.fixingSubgroup → Y (g * s) = Y g)
    (hd : ∀ g h s : ↥U, (s : Γ) ∈ F₀.fixingSubgroup → dU₁ S U Y (g * s, h) = dU₁ S U Y (g, h))
    (h : ↥U) {σ : Γ} (hσ : σ ∈ F₀.fixingSubgroup) : σ • val S (Y h) = val S (Y h) := by
  let s : ↥U := ⟨σ, hFU hσ⟩
  have hs : (s : Γ) ∈ F₀.fixingSubgroup := hσ
  have e := hd 1 h s hs
  have e1 : Y s = Y 1 := by have := hc 1 s hs; rwa [one_mul] at this
  rw [dU₁_apply, dU₁_apply, one_mul, one_mul, e1] at e
  have e2 : Y (s * h) = Y h := by
    have : s * h = h * (h⁻¹ * s * h) := by group
    rw [this]; exact hc _ _ (hN.conj_mem' s hs h)
  rw [e2, add_left_inj, sub_left_inj] at e
  have e3 : act S U s (Y h) = Y h := by
    rw [e]; apply act_eq_self_of_smul_eq; rw [Subgroup.coe_one, one_smul]
  have := congrArg (val S) e3
  rwa [val_act] at this

lemma mem_of_forall_smul_eq {F₀ : IntermediateField ℚ ℚb} {x : ℚb} (h : ∀ σ ∈ F₀.fixingSubgroup, σ x = x) : x ∈ F₀ := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup F₀]
  exact (IntermediateField.mem_fixedField_iff _ _).2 h

include hU in
theorem main (hpS : (⟨p, Fact.out⟩ : Nat.Primes) ∈ S)
    (hUS : ∃ F₀ : IntermediateField ℚ ℚb, F₀.IsUnramifiedOutside S ∧ F₀.fixingSubgroup ≤ U)
    (X : ↥U × ↥U → SU S) (hX : X ∈ levelCocyclesSr₂ U.subtype S (SUn S U))
    (hpX : (p : ℤ) • X ∈ levelCoboundariesSr₂ U.subtype S (SUn S U)) :
    ∃ z : ↥U × ↥U → ZMod p, z ∈ levelCocyclesSr₂ U.subtype S (Tr p U) ∧
      X - expo p S U ζ hζ hζS z ∈ levelCoboundariesSr₂ U.subtype S (SUn S U) := by
  classical
  obtain ⟨FU, hFU, hFUU⟩ := hUS
  obtain ⟨hXc, EX, hEX, hXl⟩ := (mem_levelCocyclesSr₂_iff _ _ _ _).1 hX
  obtain ⟨Y, hY, hYX⟩ := (mem_levelCoboundariesSr₂_iff _ _ _ _).1 hpX
  change ↥U → SU S at Y
  change dU₁ S U Y = (p : ℤ) • X at hYX

  obtain ⟨F₀, T, hF₀, hle₀, hN₀, hc₀, hT⟩ := exists_finset_of_isLevelConstantSr₁ S U hY (FU ⊔ EX) (hFU.sup hEX)
  have hF₀U : F₀.fixingSubgroup ≤ U := (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hle₀)).trans hFUU
  have hF₀X : F₀.fixingSubgroup ≤ EX.fixingSubgroup := IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hle₀)

  have hd : ∀ g h s : ↥U, (s : Γ) ∈ F₀.fixingSubgroup → dU₁ S U Y (g * s, h) = dU₁ S U Y (g, h) := by
    intro g h s hs
    rw [hYX, Pi.smul_apply, Pi.smul_apply]
    have := hXl g h s 1 (hF₀X hs) (Subgroup.one_mem _)
    rw [mul_one] at this
    rw [this]
  have hYv : ∀ (h : ↥U) (σ : Γ), σ ∈ F₀.fixingSubgroup → σ • val S (Y h) = val S (Y h) :=
    fun h σ hσ => smul_val_eq_of_dU₁ hF₀U hN₀ hc₀ hd h hσ
  have hYF₀ : ∀ h : ↥U, ((val S (Y h) : ℚbˣ) : ℚb) ∈ F₀ := by
    intro h
    apply mem_of_forall_smul_eq
    intro σ hσ
    have := congrArg (fun u : ℚbˣ => (u : ℚb)) (hYv h σ hσ)
    simpa [AlgEquiv.smul_units_def, Units.coe_map] using this

  let α : ↥U → ℚb := fun t => ((val S (root p S (Y t)) : ℚbˣ) : ℚb)
  have hαp : ∀ t, α t ^ p = ((val S (Y t) : ℚbˣ) : ℚb) := by
    intro t; simp only [α, ← Units.val_pow_eq_pow_val, val_root_pow]
  have hKf : ∀ t, (F₀ ⊔ IntermediateField.adjoin ℚ {α t}).IsUnramifiedOutside S := by
    intro t
    refine IntermediateField.IsUnramifiedOutside.sup_adjoin_simple_of_pow_mem S hp.out hpS hF₀ ?_ ?_
    · rw [hαp]; exact hYF₀ t
    · intro A hA
      rw [hαp]
      obtain ⟨h1, h2⟩ := (Additive.toMul (Y t)).2 A hA
      exact ⟨h1, by rw [← Units.val_inv_eq_inv_val]; exact h2⟩
  let F₁ : IntermediateField ℚ ℚb := F₀ ⊔ T.sup fun t => F₀ ⊔ IntermediateField.adjoin ℚ {α t}
  have hF₁ : F₁.IsUnramifiedOutside S := hF₀.sup (isUnramifiedOutside_finset_sup S T _ hKf)
  obtain ⟨F₂, hF₂, hN₂, -, hle₂⟩ := exists_normal_level S U F₁ hF₁
  have h₂₀ : F₂.fixingSubgroup ≤ F₀.fixingSubgroup := IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hle₂)

  obtain ⟨Y₁, hY₁⟩ : ∃ Y₁ : ↥U → SU S, Y₁ = fun g => root p S (Y g) := ⟨_, rfl⟩
  have hY₁p : (p : ℤ) • Y₁ = Y := by subst hY₁; exact funext fun g => p_zsmul_root p S (Y g)
  have hc : ∀ g s : ↥U, (s : Γ) ∈ F₂.fixingSubgroup → Y₁ (g * s) = Y₁ g := by
    intro g s hs; subst hY₁; simp only [hc₀ g s (h₂₀ hs)]
  have hv : ∀ g s : ↥U, (s : Γ) ∈ F₂.fixingSubgroup → act S U s (Y₁ g) = Y₁ g := by
    intro g s hs
    obtain ⟨t, ht, hgt⟩ := hT g
    have e : Y₁ g = Y₁ t := by subst hY₁; simp only [hgt]
    rw [e]
    apply act_eq_self_of_smul_eq
    subst hY₁
    apply smul_eq_of_mem_fixingSubgroup
    have hle : IntermediateField.adjoin ℚ {α t} ≤ F₂ := by
      refine le_trans ?_ hle₂
      refine le_sup_of_le_right (le_trans ?_ (Finset.le_sup (f := fun t => F₀ ⊔ IntermediateField.adjoin ℚ {α t}) ht))
      exact le_sup_right
    exact IntermediateField.fixingSubgroup_antitone hle hs
  have hY₁l : IsLevelConstantSr₁ U.subtype S Y₁ := ⟨F₂, hF₂, hc⟩

  have hdY₁ : IsLevelConstantSr₂ U.subtype S (dU₁ S U Y₁) := by
    refine ⟨F₂, hF₂, fun g g' s s' hs hs' => ?_⟩
    rw [dU₁_apply, dU₁_apply]
    have e1 : g * s * (g' * s') = g * g' * (g'⁻¹ * s * g' * s') := by group
    have hs2 : (((g'⁻¹ * s * g' * s') : ↥U) : Γ) ∈ F₂.fixingSubgroup := by
      have h1 : g'⁻¹ * s * g' ∈ F₂.fixingSubgroup.comap U.subtype := hN₂.conj_mem' s hs g'
      exact (F₂.fixingSubgroup.comap U.subtype).mul_mem h1 hs'
    rw [e1, hc _ _ hs2, hc _ _ hs, hc _ _ hs', act_mul, hv _ _ hs]

  obtain ⟨X', hX'⟩ : ∃ X' : ↥U × ↥U → SU S, X' = X - dU₁ S U Y₁ := ⟨_, rfl⟩
  have hX'c : X' ∈ cocycles₂ (SUn S U) := by rw [hX']; exact Submodule.sub_mem _ hXc (dU₁_mem_cocycles₂ S U Y₁)
  have hX'l : IsLevelConstantSr₂ U.subtype S X' := by
    have := (show IsLevelConstantSr₂ U.subtype S X from ⟨EX, hEX, hXl⟩).add (hdY₁.comp (fun v => -v))
    rw [hX', sub_eq_add_neg]
    exact this
  have hX'p : ∀ g, (p : ℤ) • X' g = 0 := by
    intro g
    have e1 : ((p : ℤ) • X) g = dU₁ S U Y g := (congrFun hYX g).symm
    have e2 : dU₁ S U Y g = (p : ℤ) • dU₁ S U Y₁ g := by rw [← hY₁p, dU₁_zsmul]; rfl
    rw [hX', Pi.sub_apply, zsmul_sub, ← e2, ← e1, Pi.smul_apply, sub_self]

  choose z hz using fun g => exists_chi_eq p S ζ hζ hζS (hX'p g)
  have hzX : expo p S U ζ hζ hζS z = X' := funext hz
  refine ⟨z, (mem_levelCocyclesSr₂_iff _ _ _ _).2 ⟨?_, ?_⟩, ?_⟩
  · rw [← expo_mem_cocycles₂_iff p S U ζ hζ hζS hU, hzX]; exact hX'c
  · obtain ⟨F, hF, hcst⟩ := hX'l
    refine ⟨F, hF, fun g g' s s' hs hs' => chi_injective p S ζ hζ hζS ?_⟩
    have := hcst g g' s s' hs hs'
    rw [← hzX] at this
    exact this
  · rw [hzX, hX', sub_sub_cancel]
    exact (mem_levelCoboundariesSr₂_iff _ _ _ _).2 ⟨Y₁, hY₁l, rfl⟩

end P2MKglob

open P2MKglob in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : (⟨p, Fact.out⟩ : Nat.Primes) ∈ S)
    (U : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hUS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), F₀.IsUnramifiedOutside S ∧ F₀.fixingSubgroup ≤ U)
    (ζ : (AlgebraicClosure ℚ)ˣ) (hζ : IsPrimitiveRoot ζ p) (hζS : ζ ∈ galoisSUnits S) (hU : ∀ σ ∈ U, σ • ζ = ζ)
    (X : ↥U × ↥U → Additive ↥(galoisSUnits S))
    (hX : X ∈ levelCocyclesSr₂ U.subtype S (Rep.res U.subtype (galoisSUnitsRep S)))
    (hpX : (p : ℤ) • X ∈ levelCoboundariesSr₂ U.subtype S (Rep.res U.subtype (galoisSUnitsRep S))) :
    ∃ z : ↥U × ↥U → ZMod p, z ∈ levelCocyclesSr₂ U.subtype S (Rep.trivial (ZMod p) ↥U (ZMod p)) ∧
      X - (fun g => Additive.ofMul (⟨ζ ^ (z g).val, Subgroup.pow_mem _ hζS _⟩ : ↥(galoisSUnits S))) ∈
        levelCoboundariesSr₂ U.subtype S (Rep.res U.subtype (galoisSUnitsRep S)) :=
  main p S U ζ hζ hζS hU hpS hUS X hX hpX

end
end S_groupCohomology_exists_levelCocyclesSr2_sub_pow_mem_levelCoboundariesSr2_of_zsmul_mem
end P2MW
export P2MW.S_groupCohomology_exists_levelCocyclesSr2_sub_pow_mem_levelCoboundariesSr2_of_zsmul_mem (solution)
