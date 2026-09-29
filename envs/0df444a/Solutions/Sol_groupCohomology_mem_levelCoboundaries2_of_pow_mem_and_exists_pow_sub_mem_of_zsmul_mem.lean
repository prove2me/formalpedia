-- Prove2me | solution 1 for groupCohomology.mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/2f0b46a6-191e-5f9b-957a-936f2b637e02

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory groupCohomology

noncomputable section
namespace P2MKloc

local notation "ℚb" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

local instance isAlgebraicQbar_kl : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_kl : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_kl : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

variable (p : ℕ) [hp : Fact p.Prime] (D : Subgroup Γ) (ζ : ℚbˣ) (hζ : IsPrimitiveRoot ζ p) (hD : ∀ σ ∈ D, σ • ζ = ζ)

abbrev Un : Rep ℤ ↥D := Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ ℚb)

abbrev Tr : Rep (ZMod p) ↥D := Rep.trivial (ZMod p) ↥D (ZMod p)

lemma Un_ρ (g : ↥D) (x : Additive ℚbˣ) : (Un D).ρ g x = Additive.ofMul ((g : Γ) • Additive.toMul x) := rfl

def act (g : ↥D) (x : Additive ℚbˣ) : Additive ℚbˣ := Additive.ofMul ((g : Γ) • Additive.toMul x)

lemma act_eq (g : ↥D) (x : Additive ℚbˣ) : (Un D).ρ g x = act D g x := rfl

lemma act_mul (g h : ↥D) (x : Additive ℚbˣ) : act D (g * h) x = act D g (act D h x) := by
  simp only [act, toMul_ofMul, Subgroup.coe_mul, mul_smul]

def dU₁ (Y : ↥D → Additive ℚbˣ) : ↥D × ↥D → Additive ℚbˣ := (d₁₂ (Un D)).hom Y
def dU₀ (b : Additive ℚbˣ) : ↥D → Additive ℚbˣ := (d₀₁ (Un D)).hom b

lemma dU₁_apply (Y : ↥D → Additive ℚbˣ) (g h : ↥D) : dU₁ D Y (g, h) = act D g (Y h) - Y (g * h) + Y g :=
  d₁₂_hom_apply (Un D) Y (g, h)

lemma dU₀_apply (b : Additive ℚbˣ) (g : ↥D) : dU₀ D b g = act D g b - b := d₀₁_hom_apply (Un D) b g

lemma dU₁_sub (Y Y' : ↥D → Additive ℚbˣ) : dU₁ D (Y - Y') = dU₁ D Y - dU₁ D Y' := map_sub (d₁₂ (Un D)).hom Y Y'

lemma dU₁_zsmul (n : ℤ) (Y : ↥D → Additive ℚbˣ) : dU₁ D (n • Y) = n • dU₁ D Y := map_zsmul (d₁₂ (Un D)).hom n Y

lemma dU₀_zsmul (n : ℤ) (b : Additive ℚbˣ) : dU₀ D (n • b) = n • dU₀ D b := map_zsmul (d₀₁ (Un D)).hom n b

lemma dU₁_dU₀ (b : Additive ℚbˣ) : dU₁ D (dU₀ D b) = 0 := by
  have := congrArg (fun f => (ModuleCat.Hom.hom f) b) (d₀₁_comp_d₁₂ (Un D))
  simp at this
  exact this

lemma dU₁_mem_cocycles₂ (Y : ↥D → Additive ℚbˣ) : dU₁ D Y ∈ cocycles₂ (Un D) := d₁₂_apply_mem_cocycles₂ (A := Un D) Y

include hζ in
lemma zeta_pow_mod (m : ℕ) : ζ ^ (m % p) = ζ ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

def chi : ZMod p →+ Additive ℚbˣ :=
  AddMonoidHom.mk' (fun n => Additive.ofMul (ζ ^ n.val)) fun a b => by
    change Additive.ofMul (ζ ^ (a + b).val) = Additive.ofMul (ζ ^ a.val) + Additive.ofMul (ζ ^ b.val)
    rw [← ofMul_mul, ← pow_add, ZMod.val_add, zeta_pow_mod p ζ hζ]

lemma chi_apply (n : ZMod p) : chi p ζ hζ n = Additive.ofMul (ζ ^ n.val) := rfl

lemma chi_injective : Function.Injective (chi p ζ hζ) := by
  intro a b h
  have h' : ζ ^ a.val = ζ ^ b.val := Additive.ofMul.injective h
  exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h')

include hD in
lemma ρ_chi (g : ↥D) (n : ZMod p) : (Un D).ρ g (chi p ζ hζ n) = chi p ζ hζ n := by
  rw [Un_ρ, chi_apply, toMul_ofMul, smul_pow', hD _ g.2]

include hD in

lemma ρ_chi' (g : ↥D) (n : ZMod p) : (Rep.ofAlgebraAutOnUnits ℚ ℚb).ρ (g : Γ) (chi p ζ hζ n) = chi p ζ hζ n :=
  ρ_chi p D ζ hζ hD g n

include hζ in
lemma zeta_val : IsPrimitiveRoot ((ζ : ℚbˣ) : ℚb) p := hζ.map_of_injective Units.coeHom_injective

lemma exists_chi_eq {x : Additive ℚbˣ} (hx : (p : ℤ) • x = 0) : ∃ n : ZMod p, chi p ζ hζ n = x := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hx' : (((Additive.toMul x : ℚbˣ)) : ℚb) ^ p = 1 := by
    have := congrArg Additive.toMul hx
    rw [toMul_zsmul, zpow_natCast, toMul_zero] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  obtain ⟨i, hi, hζi⟩ := (zeta_val p ζ hζ).eq_pow_of_pow_eq_one hx'
  refine ⟨(i : ZMod p), ?_⟩
  rw [chi_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  have : ζ ^ i = Additive.toMul x := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hζi)
  rw [this]; rfl

def expo (z : ↥D × ↥D → ZMod p) : ↥D × ↥D → Additive ℚbˣ := chi p ζ hζ ∘ z
def expo₁ (w : ↥D → ZMod p) : ↥D → Additive ℚbˣ := chi p ζ hζ ∘ w

lemma expo_eq (z : ↥D × ↥D → ZMod p) :
    expo p D ζ hζ z = (fun g => Additive.ofMul (ζ ^ (z g).val) : ↥D × ↥D → Additive ℚbˣ) := rfl

include hD in
lemma d₁₂_expo₁ (w : ↥D → ZMod p) : (d₁₂ (Un D)).hom (expo₁ p D ζ hζ w) = expo p D ζ hζ ((d₁₂ (Tr p D)).hom w) := by
  funext ⟨g, h⟩
  have e1 := map_sub (chi p ζ hζ) (w h) (w (g * h))
  have e2 := map_add (chi p ζ hζ) (w h - w (g * h)) (w g)
  rw [e1] at e2
  simp only [d₁₂_hom_apply, expo₁, expo, Function.comp_apply, Rep.trivial_ρ_apply, Representation.trivial_apply,
    Rep.res_obj_ρ, MonoidHom.coe_comp, Subgroup.coe_subtype, ρ_chi' p D ζ hζ hD]
  exact e2.symm

include hD in
lemma expo_mem_cocycles₂_iff (z : ↥D × ↥D → ZMod p) : expo p D ζ hζ z ∈ cocycles₂ (Un D) ↔ z ∈ cocycles₂ (Tr p D) := by
  refine (mem_cocycles₂_iff (A := Un D) (expo p D ζ hζ z)).trans ?_
  refine Iff.trans ?_ (mem_cocycles₂_iff (A := Tr p D) z).symm
  simp only [Rep.trivial_ρ_apply, Representation.trivial_apply]
  constructor
  · intro h g i j
    have h' := h g i j
    simp only [expo, Function.comp_apply] at h'
    rw [ρ_chi p D ζ hζ hD] at h'
    apply chi_injective p ζ hζ
    rw [map_add, map_add]; exact h'
  · intro h g i j
    simp only [expo, Function.comp_apply]
    rw [ρ_chi p D ζ hζ hD]
    have := congrArg (chi p ζ hζ) (h g i j)
    rw [map_add, map_add] at this
    exact this

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
      (∀ g s : ↥D, (s : Γ) ∈ F₀.fixingSubgroup → Y (s * g) = Y g) ∧
      ∀ g : ↥D, ∃ t ∈ T, Y g = Y t := by
  classical
  obtain ⟨F', hF', hc⟩ := hY
  haveI := hF'
  obtain ⟨F₀, hF₀, hN, hFI, hle⟩ := exists_normal_level D F'
  haveI := hFI
  haveI := hN
  let L₀ : Subgroup ↥D := F₀.fixingSubgroup.comap D.subtype
  haveI : Fintype (↥D ⧸ L₀) := Fintype.ofFinite _
  refine ⟨F₀, (Finset.univ : Finset (↥D ⧸ L₀)).image Quotient.out, hF₀, hN, fun g s hs => hc g s (hle hs), fun g s hs => ?_,
    fun g => ?_⟩
  · have : s * g = g * (g⁻¹ * s * g) := by group
    rw [this]
    have hs' : g⁻¹ * s * g ∈ L₀ := hN.conj_mem' s hs g
    exact hc g _ (hle hs')
  · refine ⟨(QuotientGroup.mk g : ↥D ⧸ L₀).out, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
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

lemma finiteDimensional_adjoin (a : ℚb) : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {a}) := by
  have := IntermediateField.adjoin.finiteDimensional ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).isIntegral)
  convert this

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
  obtain ⟨F₀, T, hF₀, hN, hcY, -, hT⟩ := exists_finset_of_isLevelConstant₁ D hY
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

include hD in

theorem partII (X : ↥D × ↥D → Additive ℚbˣ) (hX : X ∈ levelCocycles₂ D.subtype (Un D))
    (hpX : (p : ℤ) • X ∈ levelCoboundaries₂ D.subtype (Un D)) :
    ∃ z : ↥D × ↥D → ZMod p, z ∈ levelCocycles₂ D.subtype (Tr p D) ∧
      X - expo p D ζ hζ z ∈ levelCoboundaries₂ D.subtype (Un D) := by
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

  choose z hz using fun g => exists_chi_eq p ζ hζ (hX'p g)
  have hzX : expo p D ζ hζ z = X' := funext hz
  refine ⟨z, (mem_levelCocycles₂_iff _ _ _).2 ⟨?_, ?_⟩, ?_⟩
  · rw [← expo_mem_cocycles₂_iff p D ζ hζ hD, hzX]; exact hX'c
  · obtain ⟨F, hF, hcst⟩ := hX'l
    refine ⟨F, hF, fun g g' s s' hs hs' => chi_injective p ζ hζ ?_⟩
    have := hcst g g' s s' hs hs'
    rw [← hzX] at this
    exact this
  · rw [hzX, hX', sub_sub_cancel]
    exact (mem_levelCoboundaries₂_iff _ _ _).2 ⟨Y₁, hY₁l, rfl⟩

lemma toMul_act (g : ↥D) (x : Additive ℚbˣ) : ((Additive.toMul (act D g x) : ℚbˣ) : ℚb) = (g : Γ) (Additive.toMul x : ℚbˣ) := by
  simp only [act, toMul_ofMul, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe]

section H90

variable {D}
variable (c : ↥D → Additive ℚbˣ) (hc1 : ∀ g h : ↥D, c (g * h) = c g + act D g (c h))
  (F₀ : IntermediateField ℚ ℚb) [FiniteDimensional ℚ F₀]
  (hcR : ∀ g s : ↥D, (s : Γ) ∈ F₀.fixingSubgroup → c (g * s) = c g)
  (L : IntermediateField ℚ ℚb) [FiniteDimensional ℚ L] [Normal ℚ L] (hL : F₀ ≤ L)
  (hcv : ∀ g : ↥D, ((Additive.toMul (c g) : ℚbˣ) : ℚb) ∈ L)

private abbrev _root_.P2MKloc.res : Γ →* (L ≃ₐ[ℚ] L) := AlgEquiv.restrictNormalHom L

p2m_export "P2MKloc" "res"
lemma coe_res (g : Γ) (x : L) : ((res L g x : L) : ℚb) = g x := AlgEquiv.restrictNormal_commutes g L x

abbrev HD : Subgroup (L ≃ₐ[ℚ] L) := ((res L).comp D.subtype).range
abbrev K₀ : IntermediateField ℚ L := IntermediateField.fixedField (HD (D := D) L)

lemma fix_K₀ : (K₀ (D := D) L).fixingSubgroup = HD (D := D) L := IntermediateField.fixingSubgroup_fixedField _

lemma exists_lift (φ : L ≃ₐ[K₀ (D := D) L] L) :
    ∃ g : ↥D, res L g = ((IntermediateField.fixingSubgroupEquiv (K₀ (D := D) L)).symm φ : (K₀ (D := D) L).fixingSubgroup) := by
  have h : (((IntermediateField.fixingSubgroupEquiv (K₀ (D := D) L)).symm φ : (K₀ (D := D) L).fixingSubgroup) :
      (L ≃ₐ[ℚ] L)) ∈ HD (D := D) L := by
    rw [← fix_K₀ L]; exact Subtype.mem _
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg⟩

def lift (φ : L ≃ₐ[K₀ (D := D) L] L) : ↥D := (exists_lift L φ).choose

lemma res_lift (φ : L ≃ₐ[K₀ (D := D) L] L) :
    res L (lift L φ : ↥D) = ((IntermediateField.fixingSubgroupEquiv (K₀ (D := D) L)).symm φ : (K₀ (D := D) L).fixingSubgroup) :=
  (exists_lift L φ).choose_spec

lemma coe_apply_eq_lift (φ : L ≃ₐ[K₀ (D := D) L] L) (x : L) : ((φ x : L) : ℚb) = ((lift L φ : ↥D) : Γ) x := by
  rw [← coe_res L _ x, res_lift]
  rfl

include hcR hL in
lemma c_eq_of_res_eq {g g' : ↥D} (h : res L (g : Γ) = res L (g' : Γ)) : c g = c g' := by
  have hmem : ((g⁻¹ * g' : ↥D) : Γ) ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have e : ((g⁻¹ * g' : ↥D) : Γ) x = ((res L ((g⁻¹ * g' : ↥D) : Γ) ⟨x, hx⟩ : L) : ℚb) := (coe_res L _ ⟨x, hx⟩).symm
    rw [e, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, inv_mul_cancel, AlgEquiv.one_apply]
  have := hcR g (g⁻¹ * g') (IntermediateField.fixingSubgroup_antitone hL hmem)
  rw [mul_inv_cancel_left] at this
  exact this.symm

def cU (g : ↥D) : (L)ˣ :=
  Units.mk0 ⟨_, hcv g⟩ (fun h => (Additive.toMul (c g) : ℚbˣ).ne_zero (congrArg Subtype.val h))

lemma coe_cU (g : ↥D) : (((cU c L hcv g : (L)ˣ) : L) : ℚb) = (Additive.toMul (c g) : ℚbˣ) := rfl

def fL (φ : L ≃ₐ[K₀ (D := D) L] L) : (L)ˣ := cU c L hcv (lift L φ)

include hc1 hcR hL in
lemma isMulCocycle₁_fL : IsMulCocycle₁ (fL c L hcv) := by
  intro φ ψ
  apply Units.ext
  apply Subtype.ext
  rw [AlgEquiv.smul_units_def, Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  change ((Additive.toMul (c (lift L (φ * ψ))) : ℚbˣ) : ℚb) =
    ((φ (cU c L hcv (lift L ψ) : L) : L) : ℚb) * (Additive.toMul (c (lift L φ)) : ℚbˣ)
  rw [coe_apply_eq_lift, coe_cU]
  have hres : res L ((lift L (φ * ψ) : ↥D) : Γ) = res L ((lift L φ * lift L ψ : ↥D) : Γ) := by
    rw [res_lift, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, map_mul, res_lift, res_lift]
  rw [c_eq_of_res_eq c F₀ hcR L hL hres, hc1, toMul_add, Units.val_mul, toMul_act, mul_comm]

include hc1 hcR hL hcv in

lemma exists_dU₀_eq : ∃ B : Additive ℚbˣ, ∀ g : ↥D, c g = dU₀ D B g := by
  haveI : FiniteDimensional (K₀ (D := D) L) L := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units (fL c L hcv) (isMulCocycle₁_fL c hc1 F₀ hcR L hL hcv)
  have hβ0 : (((β : (L)ˣ) : L) : ℚb) ≠ 0 := fun h => β.ne_zero (Subtype.ext h)
  refine ⟨Additive.ofMul (Units.mk0 _ hβ0), fun g => ?_⟩

  have hg : res L (g : Γ) ∈ (K₀ (D := D) L).fixingSubgroup := by rw [fix_K₀]; exact ⟨g, rfl⟩
  let φ : L ≃ₐ[K₀ (D := D) L] L := IntermediateField.fixingSubgroupEquiv (K₀ (D := D) L) ⟨_, hg⟩
  have hφ : res L ((lift L φ : ↥D) : Γ) = res L (g : Γ) := by
    rw [res_lift]; simp [φ]
  have h1 := hβ φ
  rw [div_eq_iff_eq_mul, AlgEquiv.smul_units_def] at h1
  have h2 := congrArg (fun u : (L)ˣ => ((u : L) : ℚb)) h1
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mul] at h2
  rw [coe_apply_eq_lift] at h2
  change ((lift L φ : ↥D) : Γ) _ = ((Additive.toMul (c (lift L φ)) : ℚbˣ) : ℚb) * _ at h2
  rw [c_eq_of_res_eq c F₀ hcR L hL hφ, ← coe_res L, hφ, coe_res] at h2

  apply Additive.toMul.injective
  apply Units.ext
  rw [dU₀_apply, toMul_sub, Units.val_div_eq_div_val, toMul_act, toMul_ofMul, Units.val_mk0, h2, mul_div_cancel_right₀ _ hβ0]

end H90

include hD in

theorem partI (z : ↥D × ↥D → ZMod p) (hz : z ∈ levelCocycles₂ D.subtype (Tr p D))
    (hdY : expo p D ζ hζ z ∈ levelCoboundaries₂ D.subtype (Un D)) :
    z ∈ levelCoboundaries₂ D.subtype (Tr p D) := by
  classical
  obtain ⟨Y, hY, hYz⟩ := (mem_levelCoboundaries₂_iff _ _ _).1 hdY
  change ↥D → Additive ℚbˣ at Y
  change dU₁ D Y = expo p D ζ hζ z at hYz

  obtain ⟨c, hc⟩ : ∃ c : ↥D → Additive ℚbˣ, c = (p : ℤ) • Y := ⟨_, rfl⟩
  have hcl : IsLevelConstant₁ D.subtype c := by rw [hc]; exact hY.comp (fun v => (p : ℤ) • v)
  have hdc : dU₁ D c = 0 := by
    rw [hc, dU₁_zsmul, hYz]
    funext g
    change (p : ℤ) • chi p ζ hζ (z g) = 0
    rw [← map_zsmul, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, map_zero]
  have hc1 : ∀ g h : ↥D, c (g * h) = c g + act D g (c h) := by
    intro g h
    have := congrFun hdc (g, h)
    rw [dU₁_apply, Pi.zero_apply, sub_add_eq_add_sub, sub_eq_zero] at this
    rw [← this, add_comm]
  obtain ⟨F₀, T, hF₀, hN, hcR, -, hT⟩ := exists_finset_of_isLevelConstant₁ D hcl
  haveI := hF₀

  let F₁ : IntermediateField ℚ ℚb := F₀ ⊔ T.sup fun t => IntermediateField.adjoin ℚ {((Additive.toMul (c t) : ℚbˣ) : ℚb)}
  haveI hF₁ : FiniteDimensional ℚ F₁ :=
    finiteDimensional_sup' hF₀ (finiteDimensional_finset_sup _ _ fun _ => finiteDimensional_adjoin _)
  let L : IntermediateField ℚ ℚb := IntermediateField.normalClosure ℚ F₁ ℚb
  haveI : Normal ℚ L := by have := normalClosure.normal ℚ (↥F₁) ℚb; convert this <;> first | rfl | exact Subsingleton.elim _ _
  have hL₁ : F₁ ≤ L := IntermediateField.le_normalClosure F₁
  have hcv : ∀ g : ↥D, ((Additive.toMul (c g) : ℚbˣ) : ℚb) ∈ L := by
    intro g
    obtain ⟨t, ht, hgt⟩ := hT g
    rw [hgt]
    refine hL₁ (le_sup_of_le_right (Finset.le_sup
      (f := fun t => IntermediateField.adjoin ℚ {((Additive.toMul (c t) : ℚbˣ) : ℚb)}) ht) ?_)
    exact IntermediateField.mem_adjoin_simple_self ℚ _
  obtain ⟨B, hB⟩ := exists_dU₀_eq c hc1 F₀ hcR L (le_sup_left.trans hL₁) hcv

  obtain ⟨Y₂, hY₂⟩ : ∃ Y₂ : ↥D → Additive ℚbˣ, Y₂ = Y - dU₀ D (root p B) := ⟨_, rfl⟩
  have hY₂p : ∀ g, (p : ℤ) • Y₂ g = 0 := by
    intro g
    have e3 : (p : ℤ) • dU₀ D (root p B) g = c g := by
      have := congrFun (dU₀_zsmul D (p : ℤ) (root p B)) g
      rw [p_zsmul_root] at this
      rw [hB]; exact this.symm
    rw [hY₂, Pi.sub_apply, zsmul_sub, e3, hc, Pi.smul_apply, sub_self]
  have hY₂l : IsLevelConstant₁ D.subtype Y₂ := by
    have h2 : IsLevelConstant₁ D.subtype (dU₀ D (root p B)) := by
      refine ⟨IntermediateField.adjoin ℚ {((Additive.toMul (root p B) : ℚbˣ) : ℚb)}, finiteDimensional_adjoin _,
        fun g s hs => ?_⟩
      rw [dU₀_apply, dU₀_apply, act_mul]
      congr 2
      rw [act]; congr 1
      exact smul_eq_of_mem_fixingSubgroup hs
    have := hY.add (h2.comp (fun v => -v))
    rw [hY₂, sub_eq_add_neg]; exact this
  have hdY₂ : dU₁ D Y₂ = expo p D ζ hζ z := by rw [hY₂, dU₁_sub, dU₁_dU₀, sub_zero, hYz]
  choose w hw using fun g => exists_chi_eq p ζ hζ (hY₂p g)
  have hwY : expo₁ p D ζ hζ w = Y₂ := funext hw

  have hzw : (d₁₂ (Tr p D)).hom w = z := by
    have e := d₁₂_expo₁ p D ζ hζ hD w
    rw [hwY] at e
    change dU₁ D Y₂ = _ at e
    rw [hdY₂] at e
    funext g
    exact (chi_injective p ζ hζ (congrFun e g)).symm
  refine (mem_levelCoboundaries₂_iff _ _ _).2 ⟨w, ?_, hzw⟩
  obtain ⟨F, hF, hcst⟩ := hY₂l
  refine ⟨F, hF, fun g s hs => chi_injective p ζ hζ ?_⟩
  have := hcst g s hs
  rw [← hwY] at this
  exact this

end P2MKloc

open P2MKloc in
theorem solution
    {p : ℕ} [Fact p.Prime] (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (ζ : (AlgebraicClosure ℚ)ˣ) (hζ : IsPrimitiveRoot ζ p) (hD : ∀ σ ∈ D, σ • ζ = ζ) :
    (∀ z : ↥D × ↥D → ZMod p, z ∈ levelCocycles₂ D.subtype (Rep.trivial (ZMod p) ↥D (ZMod p)) →
      (fun g => Additive.ofMul (ζ ^ (z g).val) : ↥D × ↥D → Additive (AlgebraicClosure ℚ)ˣ) ∈
        levelCoboundaries₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))) →
      z ∈ levelCoboundaries₂ D.subtype (Rep.trivial (ZMod p) ↥D (ZMod p))) ∧
    (∀ X : ↥D × ↥D → Additive (AlgebraicClosure ℚ)ˣ,
      X ∈ levelCocycles₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))) →
      (p : ℤ) • X ∈ levelCoboundaries₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))) →
      ∃ z : ↥D × ↥D → ZMod p, z ∈ levelCocycles₂ D.subtype (Rep.trivial (ZMod p) ↥D (ZMod p)) ∧
        X - (fun g => Additive.ofMul (ζ ^ (z g).val)) ∈
          levelCoboundaries₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) :=
  ⟨fun z hz h => partI p D ζ hζ hD z hz h, fun X hX hpX => partII p D ζ hζ hD X hX hpX⟩

end
end S_groupCohomology_mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem
end P2MW
export P2MW.S_groupCohomology_mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem (solution)
