-- Prove2me | solution 1 for groupCohomology.nonempty_continuousH2S_coind_equiv_continuousH2Sr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/d8a4cb15-50a8-54b2-9673-7e1c2a2c79cb

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_nonempty_continuousH2S_coind_equiv_continuousH2Sr

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology

section gwcPrism

variable {Γ V : Type} [AddCommGroup V]

private lemma gwc_prism_aux (X : Γ → Γ → Γ → V)
    (hX : ∀ a b c d : Γ, X b c d - X a c d + X a b d - X a b c = 0) (a b c d : Γ) :
    X b c d = X a c d - X a b d + X a b c := by
  rw [← sub_eq_zero, ← hX a b c d]
  abel

private lemma gwc_prism (X : Γ → Γ → Γ → V) (π : Γ → Γ)
    (hX : ∀ a b c d : Γ, X b c d - X a c d + X a b d - X a b c = 0) (g₀ g₁ g₂ : Γ) :
    (X (π g₁) g₁ g₂ - X (π g₁) (π g₂) g₂) - (X (π g₀) g₀ g₂ - X (π g₀) (π g₂) g₂)
        + (X (π g₀) g₀ g₁ - X (π g₀) (π g₁) g₁) =
      X g₀ g₁ g₂ - X (π g₀) (π g₁) (π g₂) := by
  rw [gwc_prism_aux X hX (π g₀) g₀ g₁ g₂, gwc_prism_aux X hX (π g₀) (π g₁) g₁ g₂,
    gwc_prism_aux X hX (π g₀) (π g₁) (π g₂) g₂]
  abel

end gwcPrism

section gwcRetract

variable {Γ : Type} [Group Γ] {H : Subgroup Γ}

private lemma gwc_exists_retract (H : Subgroup Γ) :
    ∃ π : Γ → ↥H, (∀ (h : ↥H) (x : Γ), π ((h : Γ) * x) = h * π x) ∧ ∀ h : ↥H, π (h : Γ) = h := by
  classical
  letI := QuotientGroup.rightRel H
  choose! i hi using Quotient.mk'_surjective (α := Γ)
  let γ (g : Γ) : ↥H := ⟨g * (i (Quotient.mk' g))⁻¹,
    (QuotientGroup.rightRel_apply.1 (Quotient.eq'.1 (hi (Quotient.mk' g))))⟩
  have hmk (s : ↥H) (g : Γ) : Quotient.mk' (s.1 * g) = Quotient.mk' g :=
    Quotient.eq'.2 (QuotientGroup.rightRel_apply.2 (by simp))
  have hγ (s : ↥H) (g : Γ) : γ (s.1 * g) = s * γ g := by ext; simp [mul_assoc, γ, hmk]
  refine ⟨fun g => γ g * (γ 1)⁻¹, fun s g => ?_, fun h => ?_⟩
  · show γ ((s : Γ) * g) * (γ 1)⁻¹ = s * (γ g * (γ 1)⁻¹)
    rw [hγ s g, mul_assoc]
  · show γ (h : Γ) * (γ 1)⁻¹ = h
    have h1 := hγ h 1
    rw [mul_one] at h1
    rw [h1, mul_inv_cancel_right]

variable (π : Γ → ↥H)

private def gwcC (x γ : Γ) : ↥H := (π x)⁻¹ * π (x * γ)

private def gwcSig (x : Γ) : Γ := ((π x : ↥H) : Γ)⁻¹ * x

private lemma gwc_π_mul_gwcC (x γ : Γ) : π x * gwcC π x γ = π (x * γ) :=
  mul_inv_cancel_left _ _

private lemma gwcC_mul (x γ γ' : Γ) : gwcC π x (γ * γ') = gwcC π x γ * gwcC π (x * γ) γ' := by
  simp only [gwcC, mul_assoc, mul_inv_cancel_left]

variable {π}

private lemma gwc_π_one (hπ₂ : ∀ h : ↥H, π (h : Γ) = h) : π 1 = 1 := by
  simpa using hπ₂ 1

private lemma gwcC_coe_mul (hπ₁ : ∀ (h : ↥H) (x : Γ), π ((h : Γ) * x) = h * π x) (h : ↥H) (x γ : Γ) :
    gwcC π ((h : Γ) * x) γ = gwcC π x γ := by
  simp only [gwcC, mul_assoc, hπ₁, mul_inv_rev, inv_mul_cancel_left]

private lemma gwcC_one_coe (hπ₂ : ∀ h : ↥H, π (h : Γ) = h) (h : ↥H) : gwcC π 1 (h : Γ) = h := by
  simp only [gwcC, gwc_π_one hπ₂, inv_one, one_mul, hπ₂]

private lemma gwcC_coe_coe (hπ₂ : ∀ h : ↥H, π (h : Γ) = h) (h h' : ↥H) :
    gwcC π (h : Γ) (h' : Γ) = h' := by
  simp only [gwcC, ← Subgroup.coe_mul, hπ₂, inv_mul_cancel_left]

section normal

variable (hπ₁ : ∀ (h : ↥H) (x : Γ), π ((h : Γ) * x) = h * π x) {Λ : Subgroup Γ} (hΛ : Λ.Normal) (hΛH : Λ ≤ H)
include hπ₁ hΛ hΛH

private lemma gwcC_mul_mem_left (g : Γ) {t : Γ} (ht : t ∈ Λ) (γ : Γ) : gwcC π (g * t) γ = gwcC π g γ := by
  obtain ⟨u, hu⟩ : ∃ u : ↥H, g * t = (u : Γ) * g :=
    ⟨⟨g * t * g⁻¹, hΛH (hΛ.conj_mem t ht g)⟩, (inv_mul_cancel_right (g * t) g).symm⟩
  rw [hu, gwcC_coe_mul hπ₁]

private lemma gwc_coe_gwcC_mem (g : Γ) {t : Γ} (ht : t ∈ Λ) : ((gwcC π g t : ↥H) : Γ) ∈ Λ := by
  obtain ⟨u, hu, huΛ⟩ : ∃ u : ↥H, g * t = (u : Γ) * g ∧ (u : Γ) ∈ Λ :=
    ⟨⟨g * t * g⁻¹, hΛH (hΛ.conj_mem t ht g)⟩, (inv_mul_cancel_right (g * t) g).symm, hΛ.conj_mem t ht g⟩
  have h1 : gwcC π g t = (π g)⁻¹ * (u * π g) := by
    show (π g)⁻¹ * π (g * t) = (π g)⁻¹ * (u * π g)
    rw [hu, hπ₁]
  rw [h1]
  simpa [mul_assoc] using hΛ.conj_mem (u : Γ) huΛ ((π g : Γ)⁻¹)

private lemma gwcSig_mul_mem (g : Γ) {t : Γ} (ht : t ∈ Λ) : gwcSig π (g * t) = gwcSig π g := by
  obtain ⟨u, hu, hu'⟩ : ∃ u : ↥H, g * t = (u : Γ) * g ∧ (u : Γ) = g * t * g⁻¹ :=
    ⟨⟨g * t * g⁻¹, hΛH (hΛ.conj_mem t ht g)⟩, (inv_mul_cancel_right (g * t) g).symm, rfl⟩
  have h1 : π (g * t) = u * π g := by
    rw [← hπ₁]
    exact congrArg π hu
  simp only [gwcSig, h1, Subgroup.coe_mul, hu']
  group

end normal

end gwcRetract

section gwcCoind

variable {k : Type} [CommRing k] {Γ : Type} [Group Γ] {H : Subgroup Γ} {N : Rep.{0} k ↥H}

private lemma gwc_coe_mul (a : Rep.coind H.subtype N) (h : ↥H) (x : Γ) : a.1 ((h : Γ) * x) = N.ρ h (a.1 x) :=
  a.2 h x

variable (N) in

private def gwcMk (f : Γ → N) (hf : ∀ (h : ↥H) (x : Γ), f ((h : Γ) * x) = N.ρ h (f x)) : Rep.coind H.subtype N :=
  ⟨f, hf⟩

variable (N) in

private def gwcEv : Rep.coind H.subtype N →ₗ[k] N where
  toFun a := a.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma gwcEv_comm (g : ↥H) (a : Rep.coind H.subtype N) :
    gwcEv N ((Rep.coind H.subtype N).ρ (H.subtype g) a) = N.ρ g (gwcEv N a) := by
  show a.1 (1 * (g : Γ)) = N.ρ g (a.1 1)
  rw [one_mul, ← gwc_coe_mul a g 1, mul_one]

private def gwcSh (z : Γ × Γ → Rep.coind H.subtype N) : ↥H × ↥H → N :=
  fun h => (z ((h.1 : Γ), (h.2 : Γ))).1 1

private def gwcX (z : Γ × Γ → Rep.coind H.subtype N) (a b c : Γ) : N := (z (a⁻¹ * b, b⁻¹ * c)).1 a

private lemma gwc_apply_eq_gwcX (z : Γ × Γ → Rep.coind H.subtype N) (γ₁ γ₂ x : Γ) :
    (z (γ₁, γ₂)).1 x = gwcX z x (x * γ₁) (x * γ₁ * γ₂) := by
  simp only [gwcX, inv_mul_cancel_left]

private lemma gwcX_coe_mul (z : Γ × Γ → Rep.coind H.subtype N) (h : ↥H) (a b c : Γ) :
    gwcX z ((h : Γ) * a) ((h : Γ) * b) ((h : Γ) * c) = N.ρ h (gwcX z a b c) := by
  simp only [gwcX, mul_inv_rev, mul_assoc, inv_mul_cancel_left, gwc_coe_mul]

private lemma gwcX_cocycle {z : Γ × Γ → Rep.coind H.subtype N} (hz : z ∈ cocycles₂ (Rep.coind H.subtype N))
    (a b c d : Γ) : gwcX z b c d - gwcX z a c d + gwcX z a b d - gwcX z a b c = 0 := by
  have h : (z (b⁻¹ * c, c⁻¹ * d)).1 (a * (a⁻¹ * b)) - (z (a⁻¹ * b * (b⁻¹ * c), c⁻¹ * d)).1 a
      + (z (a⁻¹ * b, b⁻¹ * c * (c⁻¹ * d))).1 a - (z (a⁻¹ * b, b⁻¹ * c)).1 a = 0 :=
    congrArg (fun w : Rep.coind H.subtype N => w.1 a)
      ((mem_cocycles₂_def z).1 hz (a⁻¹ * b) (b⁻¹ * c) (c⁻¹ * d))
  simpa only [gwcX, mul_assoc, mul_inv_cancel_left] using h

variable (π : Γ → ↥H) (hπ₁ : ∀ (h : ↥H) (x : Γ), π ((h : Γ) * x) = h * π x)

private lemma gwc_ρ_π_ρ_gwcC (x γ : Γ) (w : N) : N.ρ (π x) (N.ρ (gwcC π x γ) w) = N.ρ (π (x * γ)) w := by
  rw [← gwc_π_mul_gwcC π x γ, map_mul, Module.End.mul_apply]

private noncomputable def gwcT₂ (y : ↥H × ↥H → N) : Γ × Γ → Rep.coind H.subtype N :=
  fun γ => gwcMk N (fun x => N.ρ (π x) (y (gwcC π x γ.1, gwcC π (x * γ.1) γ.2))) (by
    intro h x
    simp only [mul_assoc, hπ₁, map_mul, Module.End.mul_apply, gwcC_coe_mul hπ₁])

private lemma gwcT₂_apply (y : ↥H × ↥H → N) (γ₁ γ₂ x : Γ) :
    (gwcT₂ π hπ₁ y (γ₁, γ₂)).1 x = N.ρ (π x) (y (gwcC π x γ₁, gwcC π (x * γ₁) γ₂)) := rfl

private noncomputable def gwcT₁ (b : ↥H → N) : Γ → Rep.coind H.subtype N :=
  fun γ => gwcMk N (fun x => N.ρ (π x) (b (gwcC π x γ))) (by
    intro h x
    simp only [hπ₁, map_mul, Module.End.mul_apply, gwcC_coe_mul hπ₁])

private lemma gwcT₁_apply (b : ↥H → N) (γ x : Γ) :
    (gwcT₁ π hπ₁ b γ).1 x = N.ρ (π x) (b (gwcC π x γ)) := rfl

private noncomputable def gwcS (z : Γ × Γ → Rep.coind H.subtype N) : Γ → Rep.coind H.subtype N :=
  fun γ => gwcMk N (fun x => gwcX z ((π x : ↥H) : Γ) x (x * γ) - gwcX z ((π x : ↥H) : Γ) ((π (x * γ) : ↥H) : Γ) (x * γ))
    (by
      intro h x
      simp only [mul_assoc, hπ₁, Subgroup.coe_mul, gwcX_coe_mul, map_sub])

private lemma gwcS_apply (z : Γ × Γ → Rep.coind H.subtype N) (γ x : Γ) :
    (gwcS π hπ₁ z γ).1 x =
      gwcX z ((π x : ↥H) : Γ) x (x * γ) - gwcX z ((π x : ↥H) : Γ) ((π (x * γ) : ↥H) : Γ) (x * γ) := rfl

private lemma gwcS_apply_eq (z : Γ × Γ → Rep.coind H.subtype N) (γ x : Γ) :
    (gwcS π hπ₁ z γ).1 x =
      (z (gwcSig π x, γ)).1 (π x : Γ) - (z (((gwcC π x γ : ↥H) : Γ), gwcSig π (x * γ))).1 (π x : Γ) := by
  simp only [gwcS_apply, gwcX, gwcSig, gwcC, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_left]

private lemma gwcT₂_gwcSh_apply (z : Γ × Γ → Rep.coind H.subtype N) (γ₁ γ₂ x : Γ) :
    (gwcT₂ π hπ₁ (gwcSh z) (γ₁, γ₂)).1 x =
      gwcX z ((π x : ↥H) : Γ) ((π (x * γ₁) : ↥H) : Γ) ((π (x * γ₁ * γ₂) : ↥H) : Γ) := by
  simp only [gwcT₂_apply, gwcSh]
  rw [← gwc_coe_mul, mul_one]
  simp only [gwcX, gwcC, Subgroup.coe_mul, Subgroup.coe_inv]

private lemma gwcSh_gwcT₂ (hπ₂ : ∀ h : ↥H, π (h : Γ) = h) (y : ↥H × ↥H → N) : gwcSh (gwcT₂ π hπ₁ y) = y := by
  funext ⟨h₁, h₂⟩
  simp only [gwcSh, gwcT₂_apply, gwc_π_one hπ₂, gwcC_one_coe hπ₂, one_mul, gwcC_coe_coe hπ₂, map_one,
    Module.End.one_apply]

private lemma gwcT₂_mem_cocycles₂ {y : ↥H × ↥H → N} (hy : y ∈ cocycles₂ N) :
    gwcT₂ π hπ₁ y ∈ cocycles₂ (Rep.coind H.subtype N) := by
  rw [mem_cocycles₂_def] at hy ⊢
  intro g h j
  apply Subtype.ext
  funext x
  have key := congrArg (N.ρ (π x)) (hy (gwcC π x g) (gwcC π (x * g) h) (gwcC π (x * g * h) j))
  simp only [map_sub, map_add, map_zero, gwc_ρ_π_ρ_gwcC π] at key
  show N.ρ (π (x * g)) (y (gwcC π (x * g) h, gwcC π (x * g * h) j))
      - N.ρ (π x) (y (gwcC π x (g * h), gwcC π (x * (g * h)) j))
      + N.ρ (π x) (y (gwcC π x g, gwcC π (x * g) (h * j)))
      - N.ρ (π x) (y (gwcC π x g, gwcC π (x * g) h)) = 0
  rw [gwcC_mul π x g h, ← mul_assoc x g h, gwcC_mul π (x * g) h j]
  exact key

private lemma gwc_d₁₂_gwcT₁ (b : ↥H → N) :
    (d₁₂ (Rep.coind H.subtype N)).hom (gwcT₁ π hπ₁ b) = gwcT₂ π hπ₁ ((d₁₂ N).hom b) := by
  funext ⟨γ₁, γ₂⟩
  apply Subtype.ext
  funext x
  show N.ρ (π (x * γ₁)) (b (gwcC π (x * γ₁) γ₂)) - N.ρ (π x) (b (gwcC π x (γ₁ * γ₂))) + N.ρ (π x) (b (gwcC π x γ₁))
    = (gwcT₂ π hπ₁ ((d₁₂ N).hom b) (γ₁, γ₂)).1 x
  simp only [gwcT₂_apply, d₁₂_hom_apply, map_sub, map_add, gwc_ρ_π_ρ_gwcC π, gwcC_mul]

private lemma gwc_homotopy {z : Γ × Γ → Rep.coind H.subtype N} (hz : z ∈ cocycles₂ (Rep.coind H.subtype N)) :
    (d₁₂ (Rep.coind H.subtype N)).hom (gwcS π hπ₁ z) = z - gwcT₂ π hπ₁ (gwcSh z) := by
  funext ⟨γ₁, γ₂⟩
  apply Subtype.ext
  funext x
  have hp := gwc_prism (gwcX z) (fun g => ((π g : ↥H) : Γ)) (gwcX_cocycle hz) x (x * γ₁) (x * γ₁ * γ₂)
  show (gwcS π hπ₁ z γ₂).1 (x * γ₁) - (gwcS π hπ₁ z (γ₁ * γ₂)).1 x + (gwcS π hπ₁ z γ₁).1 x
    = (z (γ₁, γ₂)).1 x - (gwcT₂ π hπ₁ (gwcSh z) (γ₁, γ₂)).1 x
  simp only [gwcS_apply, gwcT₂_gwcSh_apply, gwc_apply_eq_gwcX z, ← mul_assoc]
  exact hp

section level

variable {Λ : Subgroup Γ} (hΛ : Λ.Normal) (hΛH : Λ ≤ H)
include hΛ hΛH

private lemma gwcT₂_const (y : ↥H × ↥H → N)
    (hy : ∀ (g g' s s' : ↥H), (s : Γ) ∈ Λ → (s' : Γ) ∈ Λ → y (g * s, g' * s') = y (g, g'))
    (γ₁ γ₂ t₁ t₂ : Γ) (ht₁ : t₁ ∈ Λ) (ht₂ : t₂ ∈ Λ) :
    gwcT₂ π hπ₁ y (γ₁ * t₁, γ₂ * t₂) = gwcT₂ π hπ₁ y (γ₁, γ₂) := by
  apply Subtype.ext
  funext x
  rw [gwcT₂_apply, gwcT₂_apply, gwcC_mul π x γ₁ t₁, ← mul_assoc x γ₁ t₁, gwcC_mul_mem_left hπ₁ hΛ hΛH (x * γ₁) ht₁,
    gwcC_mul π (x * γ₁) γ₂ t₂,
    hy _ _ _ _ (gwc_coe_gwcC_mem hπ₁ hΛ hΛH (x * γ₁) ht₁) (gwc_coe_gwcC_mem hπ₁ hΛ hΛH (x * γ₁ * γ₂) ht₂)]

private lemma gwcT₁_const (b : ↥H → N) (hb : ∀ (g s : ↥H), (s : Γ) ∈ Λ → b (g * s) = b g)
    (γ t : Γ) (ht : t ∈ Λ) : gwcT₁ π hπ₁ b (γ * t) = gwcT₁ π hπ₁ b γ := by
  apply Subtype.ext
  funext x
  rw [gwcT₁_apply, gwcT₁_apply, gwcC_mul π x γ t, hb _ _ (gwc_coe_gwcC_mem hπ₁ hΛ hΛH (x * γ) ht)]

private lemma gwcS_const (z : Γ × Γ → Rep.coind H.subtype N)
    (hz : ∀ g g' s s' : Γ, s ∈ Λ → s' ∈ Λ → z (g * s, g' * s') = z (g, g'))
    (γ t : Γ) (ht : t ∈ Λ) : gwcS π hπ₁ z (γ * t) = gwcS π hπ₁ z γ := by
  have hz₁ : ∀ g g' s : Γ, s ∈ Λ → z (g * s, g') = z (g, g') := fun g g' s hs => by
    simpa using hz g g' s 1 hs Λ.one_mem
  have hz₂ : ∀ g g' s' : Γ, s' ∈ Λ → z (g, g' * s') = z (g, g') := fun g g' s' hs' => by
    simpa using hz g g' 1 s' Λ.one_mem hs'
  apply Subtype.ext
  funext x
  rw [gwcS_apply_eq, gwcS_apply_eq, hz₂ _ _ t ht, gwcC_mul π x γ t, ← mul_assoc x γ t,
    gwcSig_mul_mem hπ₁ hΛ hΛH (x * γ) ht, Subgroup.coe_mul, hz₁ _ _ _ (gwc_coe_gwcC_mem hπ₁ hΛ hΛH (x * γ) ht)]

end level

end gwcCoind

section gwcLevel

variable {k : Type} [CommRing k] (S : Finset Nat.Primes) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (hK : K.IsUnramifiedOutside S)
  (hclosure : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S →
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), F ≤ L ∧ L.IsUnramifiedOutside S ∧ Normal ℚ L)
include hK hclosure

private lemma gwc_absorb (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), L.IsUnramifiedOutside S ∧ L.fixingSubgroup.Normal ∧
      L.fixingSubgroup ≤ K.fixingSubgroup ∧ L.fixingSubgroup ≤ F.fixingSubgroup := by
  obtain ⟨L, hle, hL, hLn⟩ := hclosure (K ⊔ F) (hK.sup hF)
  haveI : ∀ i : Algebra ℚ L, @Normal ℚ L _ _ i := fun i => by convert hLn; exact Subsingleton.elim _ _
  have hker := IntermediateField.restrictNormalHom_ker L
  refine ⟨L, hL, ?_, IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hle),
    IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hle)⟩
  rw [← hker]
  infer_instance

variable {N : Rep.{0} k ↥K.fixingSubgroup} (π : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ↥K.fixingSubgroup)
  (hπ₁ : ∀ (h : ↥K.fixingSubgroup) (x : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), π ((h : _) * x) = h * π x)

private lemma gwcT₂_isLevelConstant {y : ↥K.fixingSubgroup × ↥K.fixingSubgroup → N}
    (hy : IsLevelConstantSr₂ K.fixingSubgroup.subtype S y) :
    IsLevelConstantSr₂ (MonoidHom.id _) S (gwcT₂ π hπ₁ y) := by
  obtain ⟨F, hF, hyF⟩ := hy
  obtain ⟨L, hL, hLn, hLK, hLF⟩ := gwc_absorb S K hK hclosure F hF
  exact ⟨L, hL, fun g g' s s' hs hs' =>
    gwcT₂_const π hπ₁ hLn hLK y (fun a a' u u' hu hu' => hyF a a' u u' (hLF hu) (hLF hu')) g g' s s' hs hs'⟩

private lemma gwcT₁_isLevelConstant {b : ↥K.fixingSubgroup → N} (hb : IsLevelConstantSr₁ K.fixingSubgroup.subtype S b) :
    IsLevelConstantSr₁ (MonoidHom.id _) S (gwcT₁ π hπ₁ b) := by
  obtain ⟨F, hF, hbF⟩ := hb
  obtain ⟨L, hL, hLn, hLK, hLF⟩ := gwc_absorb S K hK hclosure F hF
  exact ⟨L, hL, fun g s hs => gwcT₁_const π hπ₁ hLn hLK b (fun a u hu => hbF a u (hLF hu)) g s hs⟩

private lemma gwcS_isLevelConstant
    {z : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
      Rep.coind K.fixingSubgroup.subtype N}
    (hz : IsLevelConstantSr₂ (MonoidHom.id _) S z) : IsLevelConstantSr₁ (MonoidHom.id _) S (gwcS π hπ₁ z) := by
  obtain ⟨F, hF, hzF⟩ := hz
  obtain ⟨L, hL, hLn, hLK, hLF⟩ := gwc_absorb S K hK hclosure F hF
  exact ⟨L, hL, fun g s hs =>
    gwcS_const π hπ₁ hLn hLK z (fun a a' u u' hu hu' => hzF a a' u u' (hLF hu) (hLF hu')) g s hs⟩

end gwcLevel

section gwcShapiro

variable {k : Type} [CommRing k] (S : Finset Nat.Primes) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (N : Rep.{0} k ↥K.fixingSubgroup)

private noncomputable def gwcShMap :
    continuousH2Sr (MonoidHom.id _) S (Rep.coind K.fixingSubgroup.subtype N) →ₗ[k]
      continuousH2Sr K.fixingSubgroup.subtype S N :=
  continuousH2SrMap (rH := MonoidHom.id _) (rG := K.fixingSubgroup.subtype) K.fixingSubgroup.subtype (fun _ => rfl) S
    (gwcEv N) (gwcEv_comm)

variable {S K N} (hK : K.IsUnramifiedOutside S)
  (hclosure : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S →
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), F ≤ L ∧ L.IsUnramifiedOutside S ∧ Normal ℚ L)
  (π : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ↥K.fixingSubgroup)
  (hπ₁ : ∀ (h : ↥K.fixingSubgroup) (x : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), π ((h : _) * x) = h * π x)
  (hπ₂ : ∀ h : ↥K.fixingSubgroup, π (h : _) = h)
include hK hclosure hπ₁

private lemma gwcShMap_injective : Function.Injective (gwcShMap S K N) := by
  refine (injective_iff_map_eq_zero _).2 fun q hq => ?_
  obtain ⟨z, rfl⟩ := continuousH2Srπ_surjective (MonoidHom.id _) S (Rep.coind K.fixingSubgroup.subtype N) q
  rw [gwcShMap, continuousH2SrMap_continuousH2Srπ, continuousH2Srπ_eq_zero_iff] at hq
  obtain ⟨b, hb, hbe⟩ := (mem_levelCoboundariesSr₂_iff _ S N _).1 hq
  change (d₁₂ N).hom b = gwcSh z.1 at hbe
  obtain ⟨hzc, hzl⟩ := (mem_levelCocyclesSr₂_iff _ S _ _).1 z.2
  rw [continuousH2Srπ_eq_zero_iff, mem_levelCoboundariesSr₂_iff]
  refine ⟨gwcT₁ π hπ₁ b + gwcS π hπ₁ z.1,
    (gwcT₁_isLevelConstant S K hK hclosure π hπ₁ hb).add (gwcS_isLevelConstant S K hK hclosure π hπ₁ hzl), ?_⟩
  rw [map_add, gwc_d₁₂_gwcT₁, hbe, gwc_homotopy π hπ₁ hzc]
  abel

include hπ₂ in
private lemma gwcShMap_surjective : Function.Surjective (gwcShMap S K N) := by
  intro q
  obtain ⟨y, rfl⟩ := continuousH2Srπ_surjective K.fixingSubgroup.subtype S N q
  obtain ⟨hyc, hyl⟩ := (mem_levelCocyclesSr₂_iff K.fixingSubgroup.subtype S N _).1 y.2
  refine ⟨continuousH2Srπ (MonoidHom.id _) S (Rep.coind K.fixingSubgroup.subtype N)
    ⟨gwcT₂ π hπ₁ y.1, (mem_levelCocyclesSr₂_iff _ S _ _).2
      ⟨gwcT₂_mem_cocycles₂ π hπ₁ hyc, gwcT₂_isLevelConstant S K hK hclosure π hπ₁ hyl⟩⟩, ?_⟩
  rw [gwcShMap, continuousH2SrMap_continuousH2Srπ]
  congr 1
  exact Subtype.ext (gwcSh_gwcT₂ π hπ₁ hπ₂ y.1)

include hπ₂ in
private noncomputable def gwcEquiv :
    continuousH2Sr (MonoidHom.id _) S (Rep.coind K.fixingSubgroup.subtype N) ≃ₗ[k]
      continuousH2Sr K.fixingSubgroup.subtype S N :=
  LinearEquiv.ofBijective (gwcShMap S K N)
    ⟨gwcShMap_injective hK hclosure π hπ₁, gwcShMap_surjective hK hclosure π hπ₁ hπ₂⟩

end gwcShapiro

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (hN : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup → N.ρ s n = n) :
    Nonempty (continuousH2S S (Rep.coind K.fixingSubgroup.subtype N)
      ≃ₗ[ZMod p] continuousH2Sr K.fixingSubgroup.subtype S N) := by
  have _ := hN
  obtain ⟨π, hπ₁, hπ₂⟩ := gwc_exists_retract K.fixingSubgroup
  exact ⟨gwcEquiv (N := N) hK (IntermediateField.exists_normal_isUnramifiedOutside_of_le S) π hπ₁ hπ₂⟩

#print axioms solution

end S_groupCohomology_nonempty_continuousH2S_coind_equiv_continuousH2Sr
end P2MW
export P2MW.S_groupCohomology_nonempty_continuousH2S_coind_equiv_continuousH2Sr (solution)
