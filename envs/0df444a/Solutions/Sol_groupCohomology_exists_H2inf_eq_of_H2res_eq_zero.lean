-- Prove2me | solution 1 for groupCohomology.exists_H2inf_eq_of_H2res_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/2d79df54-d84d-5d7d-aca1-c3e4819497b4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_H2inf_eq_of_H2res_eq_zero

set_option autoImplicit false

universe u

p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_exists_H2inf_eq_of_H2res_eq_zero.groupCohomology Rep"

namespace groupCohomology
p2m_export "groupCohomology" "d₁₂ H2 H2π congr H1π mem_cocycles₁_iff cocycles₂ H1π_eq_zero_iff d₁₂_hom_apply coe_mapCocycles₂ d₁₂_apply_mem_cocycles₂ H2π_comp_map_apply map mem_cocycles₂_iff d₀₁_hom_apply H2π_eq_iff H2_induction_on cocycles₁ H2π_eq_zero_iff H1"
p2m_open "groupCohomology"

section ResKerHelpers

variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G}

private theorem exists_cocycles₂_sub_d₁₂ (F : cocycles₂ A) (c : G → A) :
    ∃ F' : cocycles₂ A, (∀ p, F' p = F p - d₁₂ A c p) ∧ H2π A F' = H2π A F := by
  refine ⟨F - ⟨d₁₂ A c, d₁₂_apply_mem_cocycles₂ c⟩, fun p => rfl, ?_⟩
  rw [H2π_eq_iff]
  refine ⟨-c, funext fun p => ?_⟩
  rw [map_neg]
  change -(d₁₂ A c p) = (F p - d₁₂ A c p) - F p
  abel

private theorem cocycles₂_identity (F : cocycles₂ A) (g h j : G) :
    F (g * h, j) + F (g, h) = A.ρ g (F (h, j)) + F (g, h * j) :=
  (mem_cocycles₂_iff (⇑F)).1 F.2 g h j

variable (A) (S : Subgroup G) [hS : S.Normal]

private theorem exists_H2inf_eq_of_forall_apply_eq_zero (F : cocycles₂ A)
    (h1 : ∀ (s g : G), s ∈ S → F (s, g) = 0) (h2 : ∀ (g s : G), s ∈ S → F (g, s) = 0) :
    ∃ y : H2 (A.quotientToInvariants S),
      (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2).hom y = H2π A F := by
  have hco := cocycles₂_identity F

  have h4a : ∀ (g h s : G), s ∈ S → F (g, h * s) = F (g, h) := by
    intro g h s hs
    have e := hco g h s
    rw [h2 _ s hs, h2 h s hs, map_zero, zero_add, zero_add] at e
    exact e.symm

  have h4b : ∀ (g s h : G), s ∈ S → F (g * s, h) = F (g, h) := by
    intro g s h hs
    have e := hco g s h
    rw [h2 g s hs, h1 s h hs, map_zero, add_zero, zero_add] at e
    rw [e, show s * h = h * (h⁻¹ * s * h) by group]
    exact h4a g h _ (hS.conj_mem' s hs h)

  have h4c : ∀ (s g h : G), s ∈ S → A.ρ s (F (g, h)) = F (g, h) := by
    intro s g h hs
    have e := hco s g h
    rw [h1 s g hs, h1 s (g * h) hs, add_zero, add_zero] at e
    rw [← e, show s * g = g * (g⁻¹ * s * g) by group]
    exact h4b g _ h (hS.conj_mem' s hs g)

  have hwd : ∀ g₁ h₁ g₂ h₂ : G, g₁⁻¹ * g₂ ∈ S → h₁⁻¹ * h₂ ∈ S → F (g₁, h₁) = F (g₂, h₂) := by
    intro g₁ h₁ g₂ h₂ hg hh
    rw [show g₂ = g₁ * (g₁⁻¹ * g₂) by group, h4b g₁ _ h₂ hg,
      show h₂ = h₁ * (h₁⁻¹ * h₂) by group, h4a g₁ h₁ _ hh]

  let β : (G ⧸ S) × (G ⧸ S) → A.quotientToInvariants S := fun q =>
    Quotient.liftOn₂' q.1 q.2
      (fun g h => (⟨F (g, h), fun s => h4c s g h s.2⟩ : A.quotientToInvariants S))
      (fun g₁ h₁ g₂ h₂ hg hh => Subtype.ext
        (hwd g₁ h₁ g₂ h₂ (QuotientGroup.leftRel_apply.mp hg) (QuotientGroup.leftRel_apply.mp hh)))
  have hβ : ∀ g h : G, (β ((g : G ⧸ S), (h : G ⧸ S)) : A) = F (g, h) := fun _ _ => rfl
  have hβc : β ∈ cocycles₂ (A.quotientToInvariants S) := by
    rw [mem_cocycles₂_iff]
    intro q₁ q₂ q₃
    induction q₁ using QuotientGroup.induction_on with | H g₁ =>
    induction q₂ using QuotientGroup.induction_on with | H g₂ =>
    induction q₃ using QuotientGroup.induction_on with | H g₃ =>
    apply Subtype.ext
    show F (g₁ * g₂, g₃) + F (g₁, g₂) = A.ρ g₁ (F (g₂, g₃)) + F (g₁, g₂ * g₃)
    exact hco g₁ g₂ g₃
  refine ⟨H2π _ ⟨β, hβc⟩, ?_⟩
  rw [H2π_comp_map_apply]
  congr 1

end ResKerHelpers

end groupCohomology

theorem solution
    {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (H1 (Rep.res S.subtype A))] (x : H2 A)
    (hx : (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2).hom x = 0) :
    ∃ y : H2 (A.quotientToInvariants S),
      (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2).hom y = x := by
  have hS : S.Normal := inferInstance
  classical
  induction x using H2_induction_on with | h F₀ =>

  rw [H2π_comp_map_apply, H2π_eq_zero_iff] at hx
  obtain ⟨c', hc'⟩ := hx
  have hres : ∀ s t : S, A.ρ (s : G) (c' t) - c' (s * t) + c' s = F₀ ((s : G), (t : G)) := by
    intro s t
    have := congrFun hc' (s, t)
    rwa [d₁₂_hom_apply, coe_mapCocycles₂] at this

  let c₁ : G → A := fun g => if h : g ∈ S then c' ⟨g, h⟩ else 0
  have hc₁ : ∀ (s : G) (hs : s ∈ S), c₁ s = c' ⟨s, hs⟩ := fun s hs => by
    simp only [c₁, dif_pos hs]
  obtain ⟨F₁, hF₁, hπ₁⟩ := exists_cocycles₂_sub_d₁₂ F₀ c₁
  have hF₁S : ∀ s t : G, s ∈ S → t ∈ S → F₁ (s, t) = 0 := by
    intro s t hs ht
    rw [hF₁, d₁₂_hom_apply, ← hres ⟨s, hs⟩ ⟨t, ht⟩, hc₁ t ht, hc₁ s hs, hc₁ (s * t) (S.mul_mem hs ht)]
    exact sub_self _
  have hco₁ := cocycles₂_identity F₁

  let r : G → G := fun g => ((g : G ⧸ S)).out
  have hσ : ∀ g, (r g)⁻¹ * g ∈ S := fun g => by
    rw [← QuotientGroup.eq]
    exact QuotientGroup.out_eq' _
  have hrS : ∀ s, s ∈ S → r s ∈ S := fun s hs => by
    have := S.mul_mem (hσ s) (S.inv_mem hs)
    rw [mul_inv_cancel_right] at this
    exact (S.inv_mem_iff).1 this
  have hr_mul : ∀ (g t : G), t ∈ S → r (g * t) = r g := fun g t ht => by
    have e : ((g * t : G) : G ⧸ S) = (g : G ⧸ S) := by
      rw [QuotientGroup.eq]
      simpa [mul_inv_rev, mul_assoc] using S.inv_mem ht
    simp only [r, e]
  let c₂ : G → A := fun g => -F₁ (r g, (r g)⁻¹ * g)
  have hdc₂ : ∀ (g t : G), t ∈ S → d₁₂ A c₂ (g, t) = F₁ (g, t) := by
    intro g t ht
    rw [d₁₂_hom_apply]
    simp only [c₂]
    rw [hF₁S (r t) ((r t)⁻¹ * t) (hrS t ht) (hσ t), neg_zero, map_zero, zero_sub, hr_mul g t ht]

    have e := hco₁ (r g) ((r g)⁻¹ * g) t
    rw [hF₁S _ t (hσ g) ht, map_zero, zero_add, mul_inv_cancel_left] at e
    rw [show (r g)⁻¹ * (g * t) = (r g)⁻¹ * g * t by group, ← e]
    abel
  obtain ⟨F₂, hF₂, hπ₂⟩ := exists_cocycles₂_sub_d₁₂ F₁ c₂
  have hF₂r : ∀ (g t : G), t ∈ S → F₂ (g, t) = 0 := by
    intro g t ht
    rw [hF₂, hdc₂ g t ht, sub_self]
  have hco₂ := cocycles₂_identity F₂

  have h3a : ∀ (s g t : G), t ∈ S → F₂ (s, g * t) = F₂ (s, g) := by
    intro s g t ht
    have e := hco₂ s g t
    rw [hF₂r _ t ht, hF₂r g t ht, map_zero, zero_add, zero_add] at e
    exact e.symm
  have h3b : ∀ (s t g : G), t ∈ S → F₂ (s * t, g) = A.ρ s (F₂ (t, g)) + F₂ (s, g) := by
    intro s t g ht
    have e := hco₂ s t g
    rw [hF₂r s t ht, add_zero, show t * g = g * (g⁻¹ * t * g) by group,
      h3a s g _ (hS.conj_mem' t ht g)] at e
    exact e
  have key : ∀ g : G, ∃ a : A, ∀ s : S, F₂ ((s : G), g) = A.ρ (s : G) a - a := by
    intro g
    let ψ : cocycles₁ (Rep.res S.subtype A) := ⟨fun s => F₂ ((s : G), g), by
      rw [mem_cocycles₁_iff]
      intro s t
      exact h3b s t g t.2⟩
    have h0 : H1π _ ψ = 0 := Subsingleton.elim _ _
    rw [H1π_eq_zero_iff] at h0
    obtain ⟨a, ha⟩ := h0
    refine ⟨a, fun s => ?_⟩
    have := congrFun ha s
    rw [d₀₁_hom_apply] at this
    exact this.symm
  choose a₀ ha₀ using key
  let b : G → A := fun g => if g ∈ S then 0 else a₀ (r g)
  have hbS : ∀ s, s ∈ S → b s = 0 := fun s hs => by simp only [b, if_pos hs]
  have hb_mul : ∀ (g t : G), t ∈ S → b (g * t) = b g := by
    intro g t ht
    by_cases hg : g ∈ S
    · rw [hbS _ (S.mul_mem hg ht), hbS g hg]
    · have hgt : g * t ∉ S := fun h => hg (by simpa using S.mul_mem h (S.inv_mem ht))
      simp only [b, if_neg hg, if_neg hgt, hr_mul g t ht]
  have hF₂b : ∀ (s g : G), s ∈ S → F₂ (s, g) = A.ρ s (b g) - b g := by
    intro s g hs
    by_cases hg : g ∈ S
    · rw [hF₂r s g hg, hbS g hg, map_zero, sub_zero]
    · simp only [b, if_neg hg]
      rw [← ha₀ (r g) ⟨s, hs⟩]
      conv_lhs => rw [show g = r g * ((r g)⁻¹ * g) by group]
      exact h3a s (r g) _ (hσ g)
  obtain ⟨F₃, hF₃, hπ₃⟩ := exists_cocycles₂_sub_d₁₂ F₂ b
  have hF₃r : ∀ (g s : G), s ∈ S → F₃ (g, s) = 0 := by
    intro g s hs
    rw [hF₃, d₁₂_hom_apply, hF₂r g s hs, hbS s hs, map_zero, hb_mul g s hs]
    abel
  have hF₃l : ∀ (s g : G), s ∈ S → F₃ (s, g) = 0 := by
    intro s g hs
    rw [hF₃, d₁₂_hom_apply, hF₂b s g hs, hbS s hs, show s * g = g * (g⁻¹ * s * g) by group,
      hb_mul g _ (hS.conj_mem' s hs g)]
    abel

  obtain ⟨y, hy⟩ := exists_H2inf_eq_of_forall_apply_eq_zero A S F₃ hF₃l hF₃r
  exact ⟨y, by rw [hy, hπ₃, hπ₂, hπ₁]⟩

end S_groupCohomology_exists_H2inf_eq_of_H2res_eq_zero
end P2MW
export P2MW.S_groupCohomology_exists_H2inf_eq_of_H2res_eq_zero (solution)
