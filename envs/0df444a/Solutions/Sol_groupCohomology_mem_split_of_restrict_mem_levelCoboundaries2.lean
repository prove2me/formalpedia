-- Prove2me | solution 1 for groupCohomology.mem_split_of_restrict_mem_levelCoboundaries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/ae9db431-e3c1-54f9-bdd9-a29ab37c1124

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Theorems.Thm_groupCohomology_exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup
import Theorems.Thm_groupCohomology_unitsInflate2_mem_levelCocycles2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_mem_split_of_restrict_mem_levelCoboundaries2

set_option autoImplicit false

p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_mem_split_of_restrict_mem_levelCoboundaries2.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "d₁₂ cocycles₂ d₁₂_hom_apply d₁₂_apply_mem_cocycles₂ map mem_cocycles₂_iff IsMulCocycle₁ IsLevelConstant₁ levelCocycles₂ levelCoboundaries₂ mem_levelCoboundaries₂_iff continuousH2π unitsInflate₁ unitsInflate₂ exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup unitsInflate2_mem_levelCocycles2"
p2m_open "groupCohomology"

section GIhelpers
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω)

private noncomputable def ιA : (Rep.ofAlgebraAutOnUnits K L) →+ (Rep.ofAlgebraAutOnUnits K Ω) where
  toFun b := (Additive.ofMul (Units.map (algebraMap L Ω).toMonoidHom (Additive.toMul (α := (L)ˣ) b)) :
    Additive Ωˣ)
  map_zero' := congrArg Additive.ofMul (map_one (Units.map (algebraMap L Ω).toMonoidHom))
  map_add' b b' := congrArg Additive.ofMul
    (map_mul (Units.map (algebraMap L Ω).toMonoidHom) (Additive.toMul (α := (L)ˣ) b)
      (Additive.toMul (α := (L)ˣ) b'))

private lemma coe_ιA (b : Rep.ofAlgebraAutOnUnits K L) :
    ((Additive.toMul (α := Ωˣ) (ιA L b) : Ωˣ) : Ω) = algebraMap L Ω ((Additive.toMul (α := (L)ˣ) b : (L)ˣ) : L) :=
  rfl

private lemma ιA_injective : Function.Injective (ιA L) := by
  intro b b' h
  have h' := congrArg (fun a : Rep.ofAlgebraAutOnUnits K Ω => ((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω)) h
  simp only [coe_ιA] at h'
  exact (Additive.toMul (α := (L)ˣ)).injective (Units.ext ((algebraMap L Ω).injective h'))

private lemma coe_ρΩ (g : Ω ≃ₐ[K] Ω) (a : Rep.ofAlgebraAutOnUnits K Ω) :
    ((Additive.toMul (α := Ωˣ) ((Rep.ofAlgebraAutOnUnits K Ω).ρ g a) : Ωˣ) : Ω)
      = g ((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω) := rfl

private lemma ext_Ω {a a' : Rep.ofAlgebraAutOnUnits K Ω}
    (h : ((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω) = ((Additive.toMul (α := Ωˣ) a' : Ωˣ) : Ω)) : a = a' :=
  (Additive.toMul (α := Ωˣ)).injective (Units.ext h)

variable [Normal K L]

private lemma unitsInflate₂_eq (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ) (g h : Ω ≃ₐ[K] Ω) :
    unitsInflate₂ L f (g, h) = ιA L (f (AlgEquiv.restrictNormalHom L g, AlgEquiv.restrictNormalHom L h)) := rfl

private lemma unitsInflate₁_eq (c : (L ≃ₐ[K] L) → Additive (L)ˣ) (g : Ω ≃ₐ[K] Ω) :
    unitsInflate₁ L c g = ιA L (c (AlgEquiv.restrictNormalHom L g)) := rfl

private lemma ιA_ρ (g : Ω ≃ₐ[K] Ω) (b : Rep.ofAlgebraAutOnUnits K L) :
    ιA L ((Rep.ofAlgebraAutOnUnits K L).ρ (AlgEquiv.restrictNormalHom L g) b)
      = (Rep.ofAlgebraAutOnUnits K Ω).ρ g (ιA L b) :=
  ext_Ω (AlgEquiv.restrictNormal_commutes g L _)

private lemma restrictNormalHom_eq_one_iff (s : Ω ≃ₐ[K] Ω) :
    AlgEquiv.restrictNormalHom L s = 1 ↔ s ∈ L.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker]

end GIhelpers

end groupCohomology

namespace groupCohomology
p2m_export "groupCohomology" "d₁₂ cocycles₂ d₁₂_hom_apply d₁₂_apply_mem_cocycles₂ map mem_cocycles₂_iff IsMulCocycle₁ IsLevelConstant₁ levelCocycles₂ levelCoboundaries₂ mem_levelCoboundaries₂_iff continuousH2π unitsInflate₁ unitsInflate₂ exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup unitsInflate2_mem_levelCocycles2"
p2m_open "groupCohomology"

section T5helpers

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

private theorem exists_cocycles₂_sub_d₁₂' {A : Rep ℤ (Ω ≃ₐ[K] Ω)} (F : cocycles₂ A) (c : (Ω ≃ₐ[K] Ω) → A) :
    ∃ F' : cocycles₂ A, ∀ g h, F' (g, h) = F (g, h) - (A.ρ g (c h) - c (g * h) + c g) :=
  ⟨F - ⟨d₁₂ A c, d₁₂_apply_mem_cocycles₂ c⟩, fun g h => by
    show F (g, h) - d₁₂ A c (g, h) = _
    rw [d₁₂_hom_apply]⟩

private theorem cocycles₂_identity' {A : Rep ℤ (Ω ≃ₐ[K] Ω)} (F : cocycles₂ A) (g h j : Ω ≃ₐ[K] Ω) :
    F (g * h, j) + F (g, h) = A.ρ g (F (h, j)) + F (g, h * j) :=
  (mem_cocycles₂_iff (⇑F)).1 F.2 g h j

private theorem exists_forall_mem_fixingSubgroup_ρ_eq [Algebra.IsAlgebraic K Ω] (a : Rep.ofAlgebraAutOnUnits K Ω) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → (Rep.ofAlgebraAutOnUnits K Ω).ρ σ a = a := by
  refine ⟨IntermediateField.adjoin K {((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω)},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _), fun σ hσ => ext_Ω ?_⟩
  rw [coe_ρΩ]
  exact (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ _
    (IntermediateField.subset_adjoin K _ (Set.mem_singleton _))

private theorem conj_mem_fixingSubgroup_of_mem_map (E : IntermediateField K Ω) (g u : Ω ≃ₐ[K] Ω)
    (hu : u ∈ (E.map (g : Ω →ₐ[K] Ω)).fixingSubgroup) : g⁻¹ * u * g ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hu ⊢
  intro x hx
  have hgx : g x ∈ E.map (g : Ω →ₐ[K] Ω) := ⟨x, hx, rfl⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hu _ hgx, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

private theorem finiteDimensional_map (E : IntermediateField K Ω) [FiniteDimensional K E] (g : Ω ≃ₐ[K] Ω) :
    FiniteDimensional K (E.map (g : Ω →ₐ[K] Ω)) :=
  LinearEquiv.finiteDimensional (IntermediateField.intermediateFieldMap g E).toLinearEquiv

end T5helpers

end groupCohomology

set_option maxHeartbeats 6400000 in
theorem solution
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (L : IntermediateField K Ω) [FiniteDimensional K L] [Normal K L]
    (c : levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω))
    (hres : (fun g : (Ω ≃ₐ[L] Ω) × (Ω ≃ₐ[L] Ω) =>
        (c.1 : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → (Rep.ofAlgebraAutOnUnits K Ω))
          ((L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) g.1,
           (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) g.2))
        ∈ levelCoboundaries₂ (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom))
            (Rep.ofAlgebraAutOnUnits L Ω)) :
    continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) c ∈ {x | ∃ (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ)
          (_ : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
          (h : unitsInflate₂ L f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω)),
          x = continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ⟨unitsInflate₂ L f, h⟩} := by
  classical

  haveI hSn : L.fixingSubgroup.Normal := by
    rw [← IntermediateField.restrictNormalHom_ker L]; exact MonoidHom.normal_ker _
  have hπsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  have hπS : ∀ {s : Ω ≃ₐ[K] Ω}, s ∈ L.fixingSubgroup → AlgEquiv.restrictNormalHom L s = 1 :=
    fun {s} hs => (restrictNormalHom_eq_one_iff L s).2 hs
  obtain ⟨FL, hFL, hUL⟩ := hlevel L inferInstance
  haveI := hFL

  have hco : ∀ g h k : Ω ≃ₐ[K] Ω, c.1 (g * h, k) + c.1 (g, h) = (Rep.ofAlgebraAutOnUnits K Ω).ρ g (c.1 (h, k)) + c.1 (g, h * k) :=
    (mem_cocycles₂_iff (A := Rep.ofAlgebraAutOnUnits K Ω) _).1 c.2.1
  obtain ⟨Fc, hFc, hclc⟩ := c.2.2
  haveI := hFc

  obtain ⟨b, ⟨Fb, hFb, hblc⟩, hdb⟩ :=
    (mem_levelCoboundaries₂_iff _ (Rep.ofAlgebraAutOnUnits L Ω) _).1 hres
  haveI := hFb
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : (Ω ≃ₐ[L] Ω) → Rep.ofAlgebraAutOnUnits K Ω, ∀ τ, b₀ τ = b τ := ⟨b, fun _ => rfl⟩
  have hdb' : ∀ τ τ' : Ω ≃ₐ[L] Ω,
      (Rep.ofAlgebraAutOnUnits K Ω).ρ ((IntermediateField.fixingSubgroupEquiv L).symm τ : Ω ≃ₐ[K] Ω) (b₀ τ')
        - b₀ (τ * τ') + b₀ τ
      = c.1 (((IntermediateField.fixingSubgroupEquiv L).symm τ : Ω ≃ₐ[K] Ω),
          ((IntermediateField.fixingSubgroupEquiv L).symm τ' : Ω ≃ₐ[K] Ω)) := by
    intro τ τ'
    have e := congrFun hdb (τ, τ')
    rw [d₁₂_hom_apply] at e
    rw [hb₀, hb₀, hb₀]
    exact e
  have hblc' : ∀ τ u : Ω ≃ₐ[L] Ω, r ((IntermediateField.fixingSubgroupEquiv L).symm u : Ω ≃ₐ[K] Ω) ∈ Fb.fixingSubgroup →
      b₀ (τ * u) = b₀ τ := fun τ u hu => by rw [hb₀, hb₀]; exact hblc τ u hu
  clear hdb hblc hres

  have hε : ∀ (s : Ω ≃ₐ[K] Ω) (hs : s ∈ L.fixingSubgroup),
      ((IntermediateField.fixingSubgroupEquiv L).symm (IntermediateField.fixingSubgroupEquiv L ⟨s, hs⟩) : Ω ≃ₐ[K] Ω) = s :=
    fun s hs => by rw [MulEquiv.symm_apply_apply]

  obtain ⟨bS, hbS⟩ : ∃ bS : (Ω ≃ₐ[K] Ω) → Rep.ofAlgebraAutOnUnits K Ω, ∀ g, bS g =
      if hg : g ∈ L.fixingSubgroup then b₀ (IntermediateField.fixingSubgroupEquiv L ⟨g, hg⟩) else 0 :=
    ⟨_, fun _ => rfl⟩
  have hbS_in : ∀ (s : Ω ≃ₐ[K] Ω) (hs : s ∈ L.fixingSubgroup), bS s = b₀ (IntermediateField.fixingSubgroupEquiv L ⟨s, hs⟩) :=
    fun s hs => by rw [hbS, dif_pos hs]
  have hbS_out : ∀ (g : Ω ≃ₐ[K] Ω), g ∉ L.fixingSubgroup → bS g = 0 := fun g hg => by rw [hbS, dif_neg hg]
  have hres' : ∀ (s t : Ω ≃ₐ[K] Ω), s ∈ L.fixingSubgroup → t ∈ L.fixingSubgroup →
      (Rep.ofAlgebraAutOnUnits K Ω).ρ s (bS t) - bS (s * t) + bS s = c.1 (s, t) := by
    intro s t hs ht
    have e := hdb' (IntermediateField.fixingSubgroupEquiv L ⟨s, hs⟩) (IntermediateField.fixingSubgroupEquiv L ⟨t, ht⟩)
    rw [hε, hε, ← map_mul] at e
    rw [hbS_in s hs, hbS_in t ht, hbS_in (s * t) (L.fixingSubgroup.mul_mem hs ht)]
    exact e

  have hbS_lc : ∀ g u : Ω ≃ₐ[K] Ω, r u ∈ (Fb ⊔ FL).fixingSubgroup → bS (g * u) = bS g := by
    intro g u hu
    have huS : u ∈ L.fixingSubgroup := hUL u (IntermediateField.fixingSubgroup_antitone le_sup_right hu)
    by_cases hg : g ∈ L.fixingSubgroup
    · rw [hbS_in g hg, hbS_in (g * u) (L.fixingSubgroup.mul_mem hg huS)]
      have e := hblc' (IntermediateField.fixingSubgroupEquiv L ⟨g, hg⟩) (IntermediateField.fixingSubgroupEquiv L ⟨u, huS⟩)
        (by rw [hε]; exact IntermediateField.fixingSubgroup_antitone le_sup_left hu)
      rw [← map_mul] at e
      exact e
    · have hgu : g * u ∉ L.fixingSubgroup := fun h' => hg (by simpa using L.fixingSubgroup.mul_mem h' (L.fixingSubgroup.inv_mem huS))
      rw [hbS_out _ hgu, hbS_out _ hg]

  obtain ⟨F₁, hF₁''⟩ := exists_cocycles₂_sub_d₁₂' (A := Rep.ofAlgebraAutOnUnits K Ω) ⟨c.1, c.2.1⟩ bS
  have hF₁ : ∀ g h : Ω ≃ₐ[K] Ω, F₁ (g, h)
      = c.1 (g, h) - ((Rep.ofAlgebraAutOnUnits K Ω).ρ g (bS h) - bS (g * h) + bS g) := fun g h => hF₁'' g h
  clear hF₁''
  have hF₁S : ∀ s t : Ω ≃ₐ[K] Ω, s ∈ L.fixingSubgroup → t ∈ L.fixingSubgroup → F₁ (s, t) = 0 := by
    intro s t hs ht
    rw [hF₁, ← hres' s t hs ht]
    exact sub_self _
  have hco₁ := cocycles₂_identity' F₁
  have hr1 : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), r 1 ∈ F.fixingSubgroup := fun F => by
    rw [map_one]; exact F.fixingSubgroup.one_mem

  have hF₁r2 : ∀ (x y u : Ω ≃ₐ[K] Ω), r u ∈ (Fc ⊔ (Fb ⊔ FL)).fixingSubgroup → F₁ (x, y * u) = F₁ (x, y) := by
    intro x y u hu
    have hu1 : r u ∈ Fc.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hu
    have hu2 : r u ∈ (Fb ⊔ FL).fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_right hu
    rw [hF₁, hF₁, ← mul_assoc, hbS_lc y u hu2, hbS_lc (x * y) u hu2,
      show c.1 (x, y * u) = c.1 (x, y) by simpa using hclc x y 1 u (hr1 Fc) hu1]

  obtain ⟨rr, hrr⟩ : ∃ rr : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω), ∀ g, rr g = ((g : (Ω ≃ₐ[K] Ω) ⧸ L.fixingSubgroup)).out :=
    ⟨_, fun _ => rfl⟩
  have hσ : ∀ g, (rr g)⁻¹ * g ∈ L.fixingSubgroup := fun g => by
    rw [hrr, ← QuotientGroup.eq]; exact QuotientGroup.out_eq' _
  have hrS : ∀ s, s ∈ L.fixingSubgroup → rr s ∈ L.fixingSubgroup := fun s hs => by
    have := L.fixingSubgroup.mul_mem (hσ s) (L.fixingSubgroup.inv_mem hs)
    rw [mul_inv_cancel_right] at this
    exact (Subgroup.inv_mem_iff _).1 this
  have hr_mul : ∀ (g t : Ω ≃ₐ[K] Ω), t ∈ L.fixingSubgroup → rr (g * t) = rr g := fun g t ht => by
    have e : ((g * t : Ω ≃ₐ[K] Ω) : (Ω ≃ₐ[K] Ω) ⧸ L.fixingSubgroup) = (g : (Ω ≃ₐ[K] Ω) ⧸ L.fixingSubgroup) := by
      rw [QuotientGroup.eq]
      simpa [mul_inv_rev, mul_assoc] using L.fixingSubgroup.inv_mem ht
    rw [hrr, hrr, e]
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : (Ω ≃ₐ[K] Ω) → Rep.ofAlgebraAutOnUnits K Ω, ∀ g, c₂ g = -F₁ (rr g, (rr g)⁻¹ * g) :=
    ⟨_, fun _ => rfl⟩
  have hdc₂ : ∀ (g t : Ω ≃ₐ[K] Ω), t ∈ L.fixingSubgroup →
      (Rep.ofAlgebraAutOnUnits K Ω).ρ g (c₂ t) - c₂ (g * t) + c₂ g = F₁ (g, t) := by
    intro g t ht
    rw [hc₂, hc₂, hc₂, hF₁S (rr t) ((rr t)⁻¹ * t) (hrS t ht) (hσ t), neg_zero, map_zero, zero_sub, hr_mul g t ht]
    have e := hco₁ (rr g) ((rr g)⁻¹ * g) t
    rw [hF₁S _ t (hσ g) ht, map_zero, zero_add, mul_inv_cancel_left] at e
    rw [show (rr g)⁻¹ * (g * t) = (rr g)⁻¹ * g * t by rw [mul_assoc], ← e]
    abel

  have hc₂_lc : ∀ g u : Ω ≃ₐ[K] Ω, r u ∈ (Fc ⊔ (Fb ⊔ FL)).fixingSubgroup → c₂ (g * u) = c₂ g := by
    intro g u hu
    have huS : u ∈ L.fixingSubgroup :=
      hUL u (IntermediateField.fixingSubgroup_antitone (le_sup_right.trans le_sup_right) hu)
    rw [hc₂, hc₂, hr_mul g u huS, ← mul_assoc, hF₁r2 _ _ u hu]
  obtain ⟨F₂, hF₂⟩ := exists_cocycles₂_sub_d₁₂' F₁ c₂
  have hF₂r : ∀ (g t : Ω ≃ₐ[K] Ω), t ∈ L.fixingSubgroup → F₂ (g, t) = 0 := by
    intro g t ht
    rw [hF₂, hdc₂ g t ht, sub_self]
  have hco₂ := cocycles₂_identity' F₂

  obtain ⟨y, hy⟩ : ∃ y : (Ω ≃ₐ[K] Ω) → Rep.ofAlgebraAutOnUnits K Ω, ∀ g, y g = bS g + c₂ g := ⟨_, fun _ => rfl⟩
  have hF₂y : ∀ g h : Ω ≃ₐ[K] Ω, F₂ (g, h) = c.1 (g, h) - ((Rep.ofAlgebraAutOnUnits K Ω).ρ g (y h) - y (g * h) + y g) := by
    intro g h
    rw [hF₂, hF₁, hy, hy, hy, map_add]
    abel
  have hy_lc : ∀ g u : Ω ≃ₐ[K] Ω, r u ∈ (Fc ⊔ (Fb ⊔ FL)).fixingSubgroup → y (g * u) = y g := by
    intro g u hu
    rw [hy, hy, hc₂_lc g u hu, hbS_lc g u (IntermediateField.fixingSubgroup_antitone le_sup_right hu)]

  have h3a : ∀ (s g t : Ω ≃ₐ[K] Ω), t ∈ L.fixingSubgroup → F₂ (s, g * t) = F₂ (s, g) := by
    intro s g t ht
    have e := hco₂ s g t
    rw [hF₂r _ t ht, hF₂r g t ht, map_zero, zero_add, zero_add] at e
    exact e.symm
  have h3b : ∀ (s t g : Ω ≃ₐ[K] Ω), t ∈ L.fixingSubgroup →
      F₂ (s * t, g) = (Rep.ofAlgebraAutOnUnits K Ω).ρ s (F₂ (t, g)) + F₂ (s, g) := by
    intro s t g ht
    have e := hco₂ s t g
    rw [hF₂r s t ht, add_zero, show t * g = g * (g⁻¹ * t * g) by rw [mul_assoc, mul_inv_cancel_left],
      h3a s g _ (hSn.conj_mem' t ht g)] at e
    exact e

  have h3lc : ∀ g : Ω ≃ₐ[K] Ω, ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ s u : Ω ≃ₐ[K] Ω, u ∈ E.fixingSubgroup → F₂ (s * u, g) = F₂ (s, g) := by
    intro g
    obtain ⟨Ec, hEc, hEcF⟩ := hopen Fc hFc
    obtain ⟨Ey, hEy, hEyF⟩ := hopen (Fc ⊔ (Fb ⊔ FL)) inferInstance
    obtain ⟨Ev, hEv, hEvρ⟩ := exists_forall_mem_fixingSubgroup_ρ_eq (K := K) (y g)
    haveI := hEc; haveI := hEy; haveI := hEv
    haveI := finiteDimensional_map Ey g
    refine ⟨Ec ⊔ Ey ⊔ Ev ⊔ Ey.map (g : Ω →ₐ[K] Ω), inferInstance, fun s u hu => ?_⟩
    have huc : u ∈ Ec.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone (le_sup_left.trans (le_sup_left.trans le_sup_left)) hu
    have huy : u ∈ Ey.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone (le_sup_right.trans (le_sup_left.trans le_sup_left)) hu
    have huv : u ∈ Ev.fixingSubgroup := IntermediateField.fixingSubgroup_antitone (le_sup_right.trans le_sup_left) hu
    have hug : g⁻¹ * u * g ∈ Ey.fixingSubgroup :=
      conj_mem_fixingSubgroup_of_mem_map Ey g u (IntermediateField.fixingSubgroup_antitone le_sup_right hu)
    rw [hF₂y, hF₂y,
      show c.1 (s * u, g) = c.1 (s, g) by simpa using hclc s g u 1 (hEcF u huc) (hr1 Fc),
      map_mul, Module.End.mul_apply, hEvρ u huv, hy_lc s u (hEyF u huy),
      show s * u * g = s * g * (g⁻¹ * u * g) by simp only [mul_assoc, mul_inv_cancel_left],
      hy_lc (s * g) _ (hEyF _ hug)]
  have key : ∀ g : Ω ≃ₐ[K] Ω, ∃ a : Rep.ofAlgebraAutOnUnits K Ω, ∀ s : Ω ≃ₐ[K] Ω, s ∈ L.fixingSubgroup →
      F₂ (s, g) = (Rep.ofAlgebraAutOnUnits K Ω).ρ s a - a := by
    intro g
    obtain ⟨ψ, hψ⟩ : ∃ ψ : L.fixingSubgroup → Ωˣ, ∀ s, ψ s = Additive.toMul (α := Ωˣ) (F₂ (s, g)) := ⟨_, fun _ => rfl⟩
    have hψc : IsMulCocycle₁ ψ := by
      intro s t
      rw [hψ, hψ, hψ, Subgroup.coe_mul, h3b s t g t.2]
      rfl
    obtain ⟨E, hE, hElc⟩ := h3lc g
    have hψlc : ∃ L' : IntermediateField K Ω, FiniteDimensional K L' ∧
        ∀ σ τ : L.fixingSubgroup, (τ : Ω ≃ₐ[K] Ω) ∈ L'.fixingSubgroup → ψ (σ * τ) = ψ σ :=
      ⟨E, hE, fun σ τ hτ => by rw [hψ, hψ, Subgroup.coe_mul, hElc _ _ hτ]⟩
    obtain ⟨α, hα⟩ := exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup (k := K) L hψc hψlc
    obtain ⟨ā, hā⟩ : ∃ ā : Rep.ofAlgebraAutOnUnits K Ω, Additive.toMul (α := Ωˣ) ā = α := ⟨Additive.ofMul α, rfl⟩
    refine ⟨ā, fun s hs => ?_⟩
    have e := hα ⟨s, hs⟩
    rw [hψ, ← hā] at e
    exact (Additive.toMul (α := Ωˣ)).injective e
  choose a₀ ha₀ using key
  obtain ⟨bb, hbb⟩ : ∃ bb : (Ω ≃ₐ[K] Ω) → Rep.ofAlgebraAutOnUnits K Ω, ∀ g, bb g =
      if g ∈ L.fixingSubgroup then 0 else a₀ (rr g) := ⟨_, fun _ => rfl⟩
  have hbbS : ∀ s, s ∈ L.fixingSubgroup → bb s = 0 := fun s hs => by rw [hbb, if_pos hs]
  have hbb_mul : ∀ (g t : Ω ≃ₐ[K] Ω), t ∈ L.fixingSubgroup → bb (g * t) = bb g := by
    intro g t ht
    by_cases hg : g ∈ L.fixingSubgroup
    · rw [hbbS _ (L.fixingSubgroup.mul_mem hg ht), hbbS g hg]
    · have hgt : g * t ∉ L.fixingSubgroup := fun h' =>
        hg (by simpa using L.fixingSubgroup.mul_mem h' (L.fixingSubgroup.inv_mem ht))
      rw [hbb, hbb, if_neg hg, if_neg hgt, hr_mul g t ht]
  have hbb_lc : ∀ g u : Ω ≃ₐ[K] Ω, r u ∈ FL.fixingSubgroup → bb (g * u) = bb g :=
    fun g u hu => hbb_mul g u (hUL u hu)
  have hF₂b : ∀ (s g : Ω ≃ₐ[K] Ω), s ∈ L.fixingSubgroup → F₂ (s, g) = (Rep.ofAlgebraAutOnUnits K Ω).ρ s (bb g) - bb g := by
    intro s g hs
    by_cases hg : g ∈ L.fixingSubgroup
    · rw [hF₂r s g hg, hbbS g hg, map_zero, sub_zero]
    · rw [hbb, if_neg hg, ← ha₀ (rr g) s hs]
      conv_lhs => rw [show g = rr g * ((rr g)⁻¹ * g) by rw [mul_inv_cancel_left]]
      exact h3a s (rr g) _ (hσ g)
  obtain ⟨F₃, hF₃⟩ := exists_cocycles₂_sub_d₁₂' F₂ bb
  have hF₃r : ∀ (g s : Ω ≃ₐ[K] Ω), s ∈ L.fixingSubgroup → F₃ (g, s) = 0 := by
    intro g s hs
    rw [hF₃, hF₂r g s hs, hbbS s hs, map_zero, hbb_mul g s hs]
    abel
  have hF₃l : ∀ (s g : Ω ≃ₐ[K] Ω), s ∈ L.fixingSubgroup → F₃ (s, g) = 0 := by
    intro s g hs
    rw [hF₃, hF₂b s g hs, hbbS s hs, show s * g = g * (g⁻¹ * s * g) by rw [mul_assoc, mul_inv_cancel_left],
      hbb_mul g _ (hSn.conj_mem' s hs g)]
    abel
  have hco₃ := cocycles₂_identity' F₃

  obtain ⟨z, hz⟩ : ∃ z : (Ω ≃ₐ[K] Ω) → Rep.ofAlgebraAutOnUnits K Ω, ∀ g, z g = y g + bb g := ⟨_, fun _ => rfl⟩
  have hF₃z : ∀ g h : Ω ≃ₐ[K] Ω, F₃ (g, h) = c.1 (g, h) - ((Rep.ofAlgebraAutOnUnits K Ω).ρ g (z h) - z (g * h) + z g) := by
    intro g h
    rw [hF₃, hF₂y, hz, hz, hz, map_add]
    abel
  have hzlc : IsLevelConstant₁ r z := by
    refine ⟨Fc ⊔ (Fb ⊔ FL), inferInstance, fun g u hu => ?_⟩
    rw [hz, hz, hy_lc g u hu,
      hbb_lc g u (IntermediateField.fixingSubgroup_antitone (le_sup_right.trans le_sup_right) hu)]

  have h4a : ∀ (g h s : Ω ≃ₐ[K] Ω), s ∈ L.fixingSubgroup → F₃ (g, h * s) = F₃ (g, h) := by
    intro g h s hs
    have e := hco₃ g h s
    rw [hF₃r _ s hs, hF₃r h s hs, map_zero, zero_add, zero_add] at e
    exact e.symm
  have h4b : ∀ (g s h : Ω ≃ₐ[K] Ω), s ∈ L.fixingSubgroup → F₃ (g * s, h) = F₃ (g, h) := by
    intro g s h hs
    have e := hco₃ g s h
    rw [hF₃r g s hs, hF₃l s h hs, map_zero, add_zero, zero_add] at e
    rw [e, show s * h = h * (h⁻¹ * s * h) by rw [mul_assoc, mul_inv_cancel_left]]
    exact h4a g h _ (hSn.conj_mem' s hs h)
  have h4c : ∀ (s g h : Ω ≃ₐ[K] Ω), s ∈ L.fixingSubgroup → (Rep.ofAlgebraAutOnUnits K Ω).ρ s (F₃ (g, h)) = F₃ (g, h) := by
    intro s g h hs
    have e := hco₃ s g h
    rw [hF₃l s g hs, hF₃l s (g * h) hs, add_zero, add_zero] at e
    rw [← e, show s * g = g * (g⁻¹ * s * g) by rw [mul_assoc, mul_inv_cancel_left]]
    exact h4b g _ h (hSn.conj_mem' s hs g)

  have h8 : ∀ g h : Ω ≃ₐ[K] Ω, ∃ v : Rep.ofAlgebraAutOnUnits K L, ιA L v = F₃ (g, h) := by
    intro g h
    have hv : ((Additive.toMul (α := Ωˣ) (F₃ (g, h)) : Ωˣ) : Ω) ∈ L := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
      intro s hs
      exact congrArg (fun a : Rep.ofAlgebraAutOnUnits K Ω => ((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω)) (h4c s g h hs)
    have hne : ((Additive.toMul (α := Ωˣ) (F₃ (g, h)) : Ωˣ) : Ω) ≠ 0 := (Additive.toMul (α := Ωˣ) (F₃ (g, h))).ne_zero
    have hne' : (⟨_, hv⟩ : L) ≠ 0 := fun h0 => hne (congrArg Subtype.val h0)
    exact ⟨(Additive.ofMul (Units.mk0 (⟨_, hv⟩ : L) hne') : Additive (L)ˣ), ext_Ω rfl⟩
  choose vt hvt using h8
  obtain ⟨f, hfdef⟩ : ∃ f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ,
      ∀ p, f p = vt (Function.surjInv hπsurj p.1) (Function.surjInv hπsurj p.2) := ⟨_, fun _ => rfl⟩
  have hsec : ∀ g : Ω ≃ₐ[K] Ω, g⁻¹ * Function.surjInv hπsurj (AlgEquiv.restrictNormalHom L g) ∈ L.fixingSubgroup :=
    fun g => (restrictNormalHom_eq_one_iff L _).1
      (by rw [map_mul, map_inv, Function.surjInv_eq hπsurj, inv_mul_cancel])
  have hfF : ∀ g h : Ω ≃ₐ[K] Ω, ιA L (f (AlgEquiv.restrictNormalHom L g, AlgEquiv.restrictNormalHom L h)) = F₃ (g, h) := by
    intro g h
    rw [hfdef, hvt]
    dsimp only
    have e1 := h4b g _ (Function.surjInv hπsurj (AlgEquiv.restrictNormalHom L h)) (hsec g)
    have e2 := h4a g h _ (hsec h)
    rw [mul_inv_cancel_left] at e1 e2
    rw [e1, e2]
  have hfco : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L) := by
    refine (mem_cocycles₂_iff (A := Rep.ofAlgebraAutOnUnits K L) f).2 fun q₁ q₂ q₃ => ?_
    obtain ⟨g₁, rfl⟩ := hπsurj q₁
    obtain ⟨g₂, rfl⟩ := hπsurj q₂
    obtain ⟨g₃, rfl⟩ := hπsurj q₃
    apply ιA_injective L
    rw [map_add, map_add, ιA_ρ, ← map_mul, ← map_mul, hfF, hfF, hfF, hfF]
    exact hco₃ g₁ g₂ g₃
  have hflc : unitsInflate₂ L f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω) :=
    unitsInflate2_mem_levelCocycles2 r L ⟨FL, hFL, hUL⟩ hfco

  refine ⟨f, hfco, hflc, (Submodule.Quotient.eq _).2 ?_⟩
  refine (mem_levelCoboundaries₂_iff r _ _).2 ⟨z, hzlc, ?_⟩
  funext ⟨g, h⟩
  show _ = c.1 (g, h) - ιA L (f (AlgEquiv.restrictNormalHom L g, AlgEquiv.restrictNormalHom L h))
  rw [d₁₂_hom_apply, hfF, hF₃z]
  dsimp only
  abel

end S_groupCohomology_mem_split_of_restrict_mem_levelCoboundaries2
end P2MW
export P2MW.S_groupCohomology_mem_split_of_restrict_mem_levelCoboundaries2 (solution)
