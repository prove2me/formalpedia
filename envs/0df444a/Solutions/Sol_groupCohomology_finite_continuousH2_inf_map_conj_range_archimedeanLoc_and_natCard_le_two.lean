-- Prove2me | solution 1 for groupCohomology.finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/97bcb008-9766-5090-84c5-36efcf7f3500

import Mathlib
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory groupCohomology ExtCitation

noncomputable section

namespace P2MArchBr

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "ℚb" => (AlgebraicClosure ℚ)

lemma exists_sq_eq_neg_one : ∃ i : ℚb, i ^ 2 = -1 :=
  IsAlgClosed.exists_pow_nat_eq (-1 : ℚb) two_pos

lemma cc_apply_of_sq_eq_neg_one {j : ℚb} (hj : j ^ 2 = -1) : complexConjugation j = -j := by
  apply complexEmbedding.toRingHom.injective
  change complexEmbedding (complexConjugation j) = complexEmbedding (-j)
  rw [complexEmbedding_complexConjugation, map_neg]
  set w : ℂ := complexEmbedding j with hw
  have hw2 : w ^ 2 = -1 := by rw [hw, ← map_pow, hj, map_neg, map_one]
  have hre : w.re * w.re - w.im * w.im = -1 := by
    have := congrArg Complex.re hw2
    simpa [sq, Complex.mul_re] using this
  have him : w.re * w.im = 0 := by
    have := congrArg Complex.im hw2
    simp only [sq, Complex.mul_im, Complex.neg_im, Complex.one_im, neg_zero] at this
    linarith
  have hre0 : w.re = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · exfalso
      rw [h, mul_zero, sub_zero] at hre
      nlinarith [mul_self_nonneg w.re]
  apply Complex.ext
  · simp [hre0]
  · simp

lemma eq_zero_of_neg_eq_self {j : ℚb} (h : -j = j) : j = 0 := by
  have h2 : (2 : ℚb) * j = 0 := by
    rw [two_mul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel j
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

def cconj (g : Γ) : Γ := g * complexConjugation * g⁻¹

lemma cconj_def (g : Γ) : cconj g = g * complexConjugation * g⁻¹ := rfl

lemma cconj_mul_self (g : Γ) : cconj g * cconj g = 1 := by
  simp only [cconj]
  calc g * complexConjugation * g⁻¹ * (g * complexConjugation * g⁻¹)
        = g * (complexConjugation * (g⁻¹ * g) * complexConjugation) * g⁻¹ := by group
    _ = 1 := by rw [inv_mul_cancel, mul_one, complexConjugation_mul_self, mul_one, mul_inv_cancel]

lemma cconj_apply_of_sq_eq_neg_one (g : Γ) {j : ℚb} (hj : j ^ 2 = -1) : cconj g j = -j := by
  have hj' : (g⁻¹ j) ^ 2 = -1 := by rw [← map_pow, hj, map_neg, map_one]
  simp only [cconj, AlgEquiv.mul_apply]
  rw [cc_apply_of_sq_eq_neg_one hj', map_neg, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

lemma cconj_ne_one (g : Γ) : cconj g ≠ 1 := by
  intro h
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one
  have h1 := cconj_apply_of_sq_eq_neg_one g hi
  rw [h, AlgEquiv.one_apply] at h1
  have hi0 : i = 0 := eq_zero_of_neg_eq_self h1.symm
  rw [hi0] at hi
  norm_num at hi

def τ (g : Γ) : ℚb →+* ℂ :=
  (complexEmbedding : ℚb →ₐ[ℚ] ℂ).toRingHom.comp ((g⁻¹ : Γ) : ℚb ≃+* ℚb).toRingHom

lemma τ_apply (g : Γ) (x : ℚb) : τ g x = complexEmbedding (g⁻¹ x) := rfl

lemma τ_cconj (g : Γ) (x : ℚb) : τ g (cconj g x) = starRingEnd ℂ (τ g x) := by
  rw [τ_apply, τ_apply, cconj, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g⁻¹ g,
    inv_mul_cancel, AlgEquiv.one_apply, complexEmbedding_complexConjugation]

lemma τ_injective (g : Γ) : Function.Injective (τ g) := (τ g).injective

lemma coe_eq_one_or_eq_cc (h : ↥archimedeanDecomposition) :
    (h : Γ) = 1 ∨ (h : Γ) = complexConjugation := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h.2
  have h2 : complexConjugation ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, complexConjugation_sq]
  have hn' : (h : Γ) = complexConjugation ^ (n % 2) := by
    rw [← hn]
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left; rw [hn', h0, zpow_zero]
  · right; rw [hn', h1, zpow_one]

variable (U : Subgroup Γ) (g : Γ)

abbrev K : Subgroup Γ := archimedeanLoc.range.map (MulAut.conj g).toMonoidHom

abbrev D : Subgroup Γ := U ⊓ K g

variable {g} in
lemma eq_one_or_eq_cconj_of_mem_K {x : Γ} (hx : x ∈ K g) : x = 1 ∨ x = cconj g := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hy
  rcases coe_eq_one_or_eq_cc a with h1 | hc
  · left
    change g * archimedeanLoc a * g⁻¹ = 1
    rw [show archimedeanLoc a = (a : Γ) from rfl, h1, mul_one, mul_inv_cancel]
  · right
    change g * archimedeanLoc a * g⁻¹ = cconj g
    rw [show archimedeanLoc a = (a : Γ) from rfl, hc, cconj]

lemma cconj_mem_K : cconj g ∈ K g :=
  Subgroup.mem_map.2 ⟨complexConjugation, ⟨archimedeanGen, rfl⟩, rfl⟩

lemma coe_eq_one_or_eq_cconj (d : ↥(D U g)) : (d : Γ) = 1 ∨ (d : Γ) = cconj g :=
  eq_one_or_eq_cconj_of_mem_K d.2.2

lemma exists_level : ∃ F₀ : IntermediateField ℚ ℚb, FiniteDimensional ℚ F₀ ∧
    ∀ s : ↥(D U g), (s : Γ) ∈ F₀.fixingSubgroup → s = 1 := by
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one
  refine ⟨IntermediateField.adjoin ℚ {i},
    IntermediateField.adjoin.finiteDimensional ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic i).isIntegral, fun s hs => ?_⟩
  rcases coe_eq_one_or_eq_cconj U g s with h1 | hc
  · exact OneMemClass.coe_eq_one.1 h1
  · exfalso
    have hfix := (IntermediateField.mem_fixingSubgroup_iff (K := IntermediateField.adjoin ℚ {i}) _).1 hs i
      (IntermediateField.mem_adjoin_simple_self ℚ i)
    rw [hc, cconj_apply_of_sq_eq_neg_one g hi] at hfix
    have hi0 : i = 0 := eq_zero_of_neg_eq_self hfix
    rw [hi0] at hi
    norm_num at hi

lemma isLevelConstant₁_all {X : Type*} (u : ↥(D U g) → X) : IsLevelConstant₁ (D U g).subtype u := by
  obtain ⟨F₀, hF₀, h⟩ := exists_level U g
  exact ⟨F₀, hF₀, fun x s hs => by rw [h s hs, mul_one]⟩

lemma isLevelConstant₂_all {X : Type*} (f : ↥(D U g) × ↥(D U g) → X) : IsLevelConstant₂ (D U g).subtype f := by
  obtain ⟨F₀, hF₀, h⟩ := exists_level U g
  exact ⟨F₀, hF₀, fun x x' s s' hs hs' => by rw [h s hs, h s' hs', mul_one, mul_one]⟩

abbrev M : Rep ℤ ↥(D U g) := Rep.res (D U g).subtype (Rep.ofAlgebraAutOnUnits ℚ ℚb)

abbrev Y : Type := continuousH2 (D U g).subtype (M U g)

def unit (x : M U g) : ℚbˣ := Additive.toMul x

lemma unit_injective : Function.Injective (unit U g) := fun _ _ h => Additive.toMul.injective h

@[scoped simp] lemma unit_add (x y : M U g) : unit U g (x + y) = unit U g x * unit U g y := rfl
@[scoped simp] lemma unit_sub (x y : M U g) : unit U g (x - y) = unit U g x / unit U g y := rfl
@[scoped simp] lemma unit_zero : unit U g 0 = 1 := rfl
@[scoped simp] lemma unit_ofMul (u : ℚbˣ) : unit U g (Additive.ofMul u) = u := rfl

lemma coe_unit_ρ (d : ↥(D U g)) (x : M U g) :
    ((unit U g ((M U g).ρ d x) : ℚbˣ) : ℚb) = (d : Γ) ((unit U g x : ℚbˣ) : ℚb) := rfl

lemma ρ_one_apply (x : M U g) : (M U g).ρ 1 x = x := by
  rw [map_one]; rfl

lemma d₁₂_apply' (u : ↥(D U g) → M U g) (d e : ↥(D U g)) :
    (d₁₂ (M U g)).hom u (d, e) = (M U g).ρ d (u e) - u (d * e) + u d := rfl

lemma mem_levelCoboundaries₂_of_trivial (hD : ∀ d : ↥(D U g), d = 1) (f : ↥(D U g) × ↥(D U g) → M U g) :
    f ∈ levelCoboundaries₂ (D U g).subtype (M U g) := by
  refine (mem_levelCoboundaries₂_iff _ _ _).2 ⟨fun _ => f (1, 1), isLevelConstant₁_const _ _, ?_⟩
  funext ⟨d, e⟩
  obtain rfl := hD d
  obtain rfl := hD e
  rw [d₁₂_apply', ρ_one_apply, sub_add_cancel]

theorem subsingleton_of_not_mem (hU : cconj g ∉ U) : Subsingleton (Y U g) := by
  have hD : ∀ d : ↥(D U g), d = 1 := fun d => by
    rcases coe_eq_one_or_eq_cconj U g d with h | h
    · exact OneMemClass.coe_eq_one.1 h
    · exact absurd (h ▸ d.2.1) hU
  refine ⟨fun y₁ y₂ => ?_⟩
  obtain ⟨f₁, rfl⟩ := continuousH2π_surjective' y₁
  obtain ⟨f₂, rfl⟩ := continuousH2π_surjective' y₂
  rw [← sub_eq_zero, ← map_sub, continuousH2π_eq_zero_iff]
  exact mem_levelCoboundaries₂_of_trivial U g hD _
where
  continuousH2π_surjective' : Function.Surjective (continuousH2π (D U g).subtype (M U g)) := Submodule.mkQ_surjective _

section Real

variable (hU : cconj g ∈ U)

def γ₀ : ↥(D U g) := ⟨cconj g, hU, cconj_mem_K g⟩

@[scoped simp] lemma coe_γ₀ : (γ₀ U g hU : Γ) = cconj g := rfl

lemma γ₀_mul_self : γ₀ U g hU * γ₀ U g hU = 1 := Subtype.ext (cconj_mul_self g)

lemma γ₀_ne_one : γ₀ U g hU ≠ 1 := fun h => cconj_ne_one g (congrArg Subtype.val h)

lemma eq_one_or_eq_γ₀ (d : ↥(D U g)) : d = 1 ∨ d = γ₀ U g hU := by
  rcases coe_eq_one_or_eq_cconj U g d with h | h
  · exact Or.inl (OneMemClass.coe_eq_one.1 h)
  · exact Or.inr (Subtype.ext h)

def nm (m : M U g) : M U g := (M U g).ρ (γ₀ U g hU) m + m

def inv2 (f : ↥(D U g) × ↥(D U g) → M U g) : M U g := f (γ₀ U g hU, γ₀ U g hU) + f (1, 1)

lemma inv2_sub (f f' : ↥(D U g) × ↥(D U g) → M U g) :
    inv2 U g hU (f - f') = inv2 U g hU f - inv2 U g hU f' := by
  simp only [inv2, Pi.sub_apply]; abel

lemma ρ_inv2 {f : ↥(D U g) × ↥(D U g) → M U g} (hf : f ∈ cocycles₂ (M U g)) :
    (M U g).ρ (γ₀ U g hU) (inv2 U g hU f) = inv2 U g hU f := by
  have h := (mem_cocycles₂_iff f).1 hf (γ₀ U g hU) (γ₀ U g hU) (γ₀ U g hU)
  have h1 : f (1, γ₀ U g hU) = f (1, 1) := cocycles₂_map_one_fst ⟨f, hf⟩ _
  have h2 : f (γ₀ U g hU, 1) = (M U g).ρ (γ₀ U g hU) (f (1, 1)) := cocycles₂_map_one_snd ⟨f, hf⟩ _
  rw [γ₀_mul_self, h1, h2, ← map_add] at h
  rw [inv2, ← h, add_comm]

lemma inv2_d₁₂ (u : ↥(D U g) → M U g) : inv2 U g hU ((d₁₂ (M U g)).hom u) = nm U g hU (u (γ₀ U g hU)) := by
  rw [inv2, nm, d₁₂_apply', d₁₂_apply', γ₀_mul_self, mul_one, ρ_one_apply]
  abel

def lift (f : ↥(D U g) × ↥(D U g) → M U g) (m : M U g) : ↥(D U g) → M U g :=
  fun d => by classical exact if d = 1 then f (1, 1) else m

lemma lift_one (f : ↥(D U g) × ↥(D U g) → M U g) (m : M U g) : lift U g f m 1 = f (1, 1) := by
  simp [lift]

lemma lift_γ₀ (f : ↥(D U g) × ↥(D U g) → M U g) (m : M U g) : lift U g f m (γ₀ U g hU) = m := by
  simp [lift, γ₀_ne_one]

lemma d₁₂_lift_eq {f : ↥(D U g) × ↥(D U g) → M U g} (hf : f ∈ cocycles₂ (M U g)) (m : M U g)
    (hm : inv2 U g hU f = nm U g hU m) : (d₁₂ (M U g)).hom (lift U g f m) = f := by
  have h1 : ∀ e, f (1, e) = f (1, 1) := fun e => cocycles₂_map_one_fst ⟨f, hf⟩ e
  have h2 : ∀ d, f (d, 1) = (M U g).ρ d (f (1, 1)) := fun d => cocycles₂_map_one_snd ⟨f, hf⟩ d
  have h3 : f (γ₀ U g hU, γ₀ U g hU) = nm U g hU m - f (1, 1) := by
    rw [← hm, inv2, add_sub_cancel_right]
  funext ⟨d, e⟩
  rw [d₁₂_apply']
  rcases eq_one_or_eq_γ₀ U g hU d with rfl | rfl <;> rcases eq_one_or_eq_γ₀ U g hU e with rfl | rfl
  · rw [mul_one, lift_one, ρ_one_apply, sub_add_cancel]
  · rw [one_mul, lift_γ₀, lift_one, ρ_one_apply, sub_self, zero_add]
    exact (h1 _).symm
  · rw [mul_one, lift_one, lift_γ₀, sub_add_cancel]
    exact (h2 _).symm
  · rw [γ₀_mul_self, lift_γ₀, lift_one, h3, nm]
    abel

lemma mem_levelCoboundaries₂_of_inv2_eq {f : ↥(D U g) × ↥(D U g) → M U g} (hf : f ∈ cocycles₂ (M U g)) (m : M U g)
    (hm : inv2 U g hU f = nm U g hU m) : f ∈ levelCoboundaries₂ (D U g).subtype (M U g) :=
  (mem_levelCoboundaries₂_iff _ _ _).2 ⟨lift U g f m, isLevelConstant₁_all U g _, d₁₂_lift_eq U g hU hf m hm⟩

private def _root_.P2MArchBr.val (x : M U g) : ℂ := τ g ((unit U g x : ℚbˣ) : ℚb)

p2m_export "P2MArchBr" "val"
lemma val_ne_zero (x : M U g) : val U g x ≠ 0 :=
  (map_ne_zero (τ g)).2 (unit U g x).ne_zero

lemma val_add (x y : M U g) : val U g (x + y) = val U g x * val U g y := by
  rw [val, unit_add, Units.val_mul, map_mul]; rfl

lemma val_sub (x y : M U g) : val U g (x - y) = val U g x / val U g y := by
  rw [val, unit_sub, Units.val_div_eq_div_val, map_div₀]; rfl

lemma val_ρ_γ₀ (x : M U g) : val U g ((M U g).ρ (γ₀ U g hU) x) = starRingEnd ℂ (val U g x) := by
  rw [val, coe_unit_ρ, coe_γ₀, τ_cconj]; rfl

lemma val_im_eq_zero_of_fixed {x : M U g} (hx : (M U g).ρ (γ₀ U g hU) x = x) : (val U g x).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← val_ρ_γ₀ U g hU, hx]

lemma val_nm (m : M U g) : val U g (nm U g hU m) = (Complex.normSq (val U g m) : ℂ) := by
  rw [nm, val_add, val_ρ_γ₀, mul_comm, Complex.mul_conj]

lemma val_nm_re_pos (m : M U g) : 0 < (val U g (nm U g hU m)).re := by
  rw [val_nm, Complex.ofReal_re]
  exact Complex.normSq_pos.2 (val_ne_zero U g m)

lemma im_eq_zero_of_sq {w : ℂ} (him : (w ^ 2).im = 0) (hre : 0 < (w ^ 2).re) : w.im = 0 := by
  have h1 : (w ^ 2).im = 2 * w.re * w.im := by simp [sq, Complex.mul_im]; ring
  have h2 : (w ^ 2).re = w.re * w.re - w.im * w.im := by simp [sq, Complex.mul_re]
  by_contra hne
  have hre0 : w.re = 0 := by
    rw [h1] at him
    have := mul_eq_zero.1 him
    rcases this with h | h
    · simpa using h
    · exact absurd h hne
  rw [h2, hre0, zero_mul, zero_sub] at hre
  have := mul_self_nonneg w.im
  linarith

lemma exists_nm_eq {x : M U g} (hx : (M U g).ρ (γ₀ U g hU) x = x) (hpos : 0 < (val U g x).re) :
    ∃ m : M U g, nm U g hU m = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((unit U g x : ℚbˣ) : ℚb) two_pos
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact (unit U g x).ne_zero (by rw [← hz]; simp)

  have hsq : τ g z ^ 2 = val U g x := by rw [← map_pow, hz]; rfl
  have hzim : (τ g z).im = 0 :=
    im_eq_zero_of_sq (by rw [hsq]; exact val_im_eq_zero_of_fixed U g hU hx) (by rw [hsq]; exact hpos)

  have hcz : cconj g z = z := by
    apply τ_injective g
    rw [τ_cconj]
    exact Complex.conj_eq_iff_im.2 hzim
  refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
  apply unit_injective U g
  ext
  rw [nm, unit_add, Units.val_mul, coe_unit_ρ, coe_γ₀, unit_ofMul, Units.val_mk0, hcz, ← sq, hz]

lemma sub_mem_levelCoboundaries₂ {f₁ f₂ : ↥(D U g) × ↥(D U g) → M U g}
    (hf₁ : f₁ ∈ cocycles₂ (M U g)) (hf₂ : f₂ ∈ cocycles₂ (M U g))
    (h : (0 < (val U g (inv2 U g hU f₁)).re) ↔ (0 < (val U g (inv2 U g hU f₂)).re)) :
    f₁ - f₂ ∈ levelCoboundaries₂ (D U g).subtype (M U g) := by
  have hf : f₁ - f₂ ∈ cocycles₂ (M U g) := sub_mem hf₁ hf₂

  have hfix : (M U g).ρ (γ₀ U g hU) (inv2 U g hU (f₁ - f₂)) = inv2 U g hU (f₁ - f₂) := ρ_inv2 U g hU hf
  have hpos : 0 < (val U g (inv2 U g hU (f₁ - f₂))).re := by
    rw [inv2_sub, val_sub]
    have him₁ := val_im_eq_zero_of_fixed U g hU (ρ_inv2 U g hU hf₁)
    have him₂ := val_im_eq_zero_of_fixed U g hU (ρ_inv2 U g hU hf₂)
    have hne₁ := val_ne_zero U g (inv2 U g hU f₁)
    have hne₂ := val_ne_zero U g (inv2 U g hU f₂)
    set z₁ := val U g (inv2 U g hU f₁) with hz₁
    set z₂ := val U g (inv2 U g hU f₂) with hz₂
    have e₁ : z₁ = (z₁.re : ℂ) := (Complex.ext rfl (by simp [him₁]))
    have e₂ : z₂ = (z₂.re : ℂ) := (Complex.ext rfl (by simp [him₂]))
    have hr₁ : z₁.re ≠ 0 := fun h0 => hne₁ (by rw [e₁, h0, Complex.ofReal_zero])
    have hr₂ : z₂.re ≠ 0 := fun h0 => hne₂ (by rw [e₂, h0, Complex.ofReal_zero])
    rw [e₁, e₂, ← Complex.ofReal_div, Complex.ofReal_re]
    rcases lt_or_gt_of_ne hr₁ with hn₁ | hp₁
    · have hn₂ : z₂.re < 0 := lt_of_le_of_ne (not_lt.1 fun hp₂ => (not_lt.2 hn₁.le) (h.2 hp₂)) hr₂
      exact div_pos_of_neg_of_neg hn₁ hn₂
    · exact div_pos hp₁ (h.1 hp₁)
  obtain ⟨m, hm⟩ := exists_nm_eq U g hU hfix hpos
  exact mem_levelCoboundaries₂_of_inv2_eq U g hU hf m hm.symm

include hU in

theorem finite_and_natCard_le_two_of_mem : Finite (Y U g) ∧ Nat.card (Y U g) ≤ 2 := by
  have hπ : Function.Surjective (continuousH2π (D U g).subtype (M U g)) := Submodule.mkQ_surjective _
  let s : Y U g → ↥(levelCocycles₂ (D U g).subtype (M U g)) := Function.surjInv hπ
  have hs : ∀ y, continuousH2π (D U g).subtype (M U g) (s y) = y := Function.surjInv_eq hπ
  let ι : Y U g → Prop := fun y => 0 < (val U g (inv2 U g hU (s y : ↥(D U g) × ↥(D U g) → M U g))).re
  have hι : Function.Injective ι := by
    intro y₁ y₂ h12
    have key : continuousH2π (D U g).subtype (M U g) (s y₁) = continuousH2π (D U g).subtype (M U g) (s y₂) := by
      rw [← sub_eq_zero, ← map_sub, continuousH2π_eq_zero_iff]
      exact sub_mem_levelCoboundaries₂ U g hU (s y₁).2.1 (s y₂).2.1 (iff_of_eq h12)
    rwa [hs, hs] at key
  refine ⟨Finite.of_injective ι hι, ?_⟩
  have := Nat.card_le_card_of_injective ι hι
  simpa using this

end Real

theorem main :
    Finite (Y U g) ∧ Nat.card (Y U g) ≤ 2 ∧ (g * complexConjugation * g⁻¹ ∉ U → Subsingleton (Y U g)) := by
  by_cases hU : cconj g ∈ U
  · obtain ⟨h1, h2⟩ := finite_and_natCard_le_two_of_mem U g hU
    exact ⟨h1, h2, fun h => absurd hU h⟩
  · haveI : Subsingleton (Y U g) := subsingleton_of_not_mem U g hU
    haveI : Finite (Y U g) := Finite.of_subsingleton
    exact ⟨inferInstance, (Finite.card_le_one_iff_subsingleton.2 inferInstance).trans one_le_two, fun _ => inferInstance⟩

end P2MArchBr
p2m_reactivate "P2MW.S_groupCohomology_finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two.P2MArchBr"

end
p2m_reactivate "P2MW.S_groupCohomology_finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two.P2MArchBr"

open P2MArchBr in
theorem solution
    (U : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Finite (continuousH2 (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
        (Rep.res (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) ∧
    Nat.card (continuousH2 (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
        (Rep.res (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) ≤ 2 ∧
    (g * complexConjugation * g⁻¹ ∉ U →
      Subsingleton (continuousH2 (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
        (Rep.res (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))))) :=
  P2MArchBr.main U g

end S_groupCohomology_finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two
end P2MW
export P2MW.S_groupCohomology_finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two (solution)
