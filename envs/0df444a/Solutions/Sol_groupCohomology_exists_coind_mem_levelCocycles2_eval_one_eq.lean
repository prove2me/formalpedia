-- Prove2me | solution 1 for groupCohomology.exists_coind_mem_levelCocycles2_eval_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/27dff168-4ef2-5aef-ad73-6be49129f145

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_coind_mem_levelCocycles2_eval_one_eq

set_option autoImplicit false

universe u

open CategoryTheory

namespace P2mS26U5

open IntermediateField groupCohomology

section levels

variable {G : Type u} [Group G] {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}

theorem exists_isGalois_ge (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F' ∧ IsGalois ℚ F' ∧ F ≤ F' := by
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance
    rfl
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ F (AlgebraicClosure ℚ)
  haveI : Normal ℚ L := normalClosure.normal ℚ F (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ L := ⟨⟩
  exact ⟨L, inferInstance, inferInstance, IntermediateField.le_normalClosure F⟩

theorem lc₁ {X : Type*} {f : G → X} (hf : IsLevelConstant₁ r f) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      ∀ g s : G, r s ∈ F.fixingSubgroup → f (g * s) = f g ∧ f (s * g) = f g := by
  obtain ⟨F₀, hF₀, h⟩ := hf
  haveI := hF₀
  obtain ⟨F, hF, hG, hle⟩ := exists_isGalois_ge F₀
  haveI := hG
  have hN : (F.fixingSubgroup.comap r).Normal := inferInstance
  refine ⟨F, hF, hG, fun g s hs => ⟨h g s (fixingSubgroup_antitone hle hs), ?_⟩⟩
  have hs' : g⁻¹ * s * g ∈ F.fixingSubgroup.comap r := by
    simpa using hN.conj_mem s hs g⁻¹
  have := h g (g⁻¹ * s * g) (fixingSubgroup_antitone hle hs')
  rwa [show g * (g⁻¹ * s * g) = s * g by group] at this

theorem lc₂ {X : Type*} {f : G × G → X} (hf : IsLevelConstant₂ r f) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      ∀ g g' s : G, r s ∈ F.fixingSubgroup →
        f (g * s, g') = f (g, g') ∧ f (s * g, g') = f (g, g') ∧
        f (g, g' * s) = f (g, g') ∧ f (g, s * g') = f (g, g') := by
  obtain ⟨F₀, hF₀, h⟩ := hf
  haveI := hF₀
  obtain ⟨F, hF, hG, hle⟩ := exists_isGalois_ge F₀
  haveI := hG
  have hN : (F.fixingSubgroup.comap r).Normal := inferInstance
  refine ⟨F, hF, hG, fun g g' s hs => ?_⟩
  have h1 : r 1 ∈ F₀.fixingSubgroup := by rw [map_one]; exact one_mem _
  have hs₀ : r s ∈ F₀.fixingSubgroup := fixingSubgroup_antitone hle hs
  have hcg : r (g⁻¹ * s * g) ∈ F₀.fixingSubgroup :=
    fixingSubgroup_antitone hle (by simpa using hN.conj_mem s hs g⁻¹)
  have hcg' : r (g'⁻¹ * s * g') ∈ F₀.fixingSubgroup :=
    fixingSubgroup_antitone hle (by simpa using hN.conj_mem s hs g'⁻¹)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h g g' s 1 hs₀ h1
  · simpa [show g * (g⁻¹ * s * g) = s * g by group] using h g g' (g⁻¹ * s * g) 1 hcg h1
  · simpa using h g g' 1 s h1 hs₀
  · simpa [show g' * (g'⁻¹ * s * g') = s * g' by group] using h g g' 1 (g'⁻¹ * s * g') h1 hcg'

theorem out_coe_eq (U : Subgroup G) (g : G) : ∃ u ∈ U, ((g : G ⧸ U).out : G) = g * u := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  exact ⟨u, u.2, hu⟩

end levels

section smooth

variable {k G : Type u} [CommRing k] [Group G]
  {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} {M : Rep k G}
  (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → M.ρ s m = m)
include hsm

theorem exists_level_forall_of_finite {ι : Type*} [Finite ι] (v : ι → M) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ i s, r s ∈ F.fixingSubgroup → M.ρ s (v i) = v i := by
  choose Fi hFi hfix using fun i => hsm (v i)
  haveI := hFi
  exact ⟨⨆ i, Fi i, finiteDimensional_iSup_of_finite, fun i s hs =>
    hfix i s (fixingSubgroup_antitone (le_iSup Fi i) hs)⟩

theorem exists_level₁ {y : G → M} (hy : IsLevelConstant₁ r y) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      (∀ g s : G, r s ∈ F.fixingSubgroup → y (g * s) = y g ∧ y (s * g) = y g) ∧
      (∀ g s : G, r s ∈ F.fixingSubgroup → M.ρ s (y g) = y g) := by
  obtain ⟨F₁, hF₁, hG₁, h₁⟩ := lc₁ hy
  haveI := hF₁; haveI := hG₁
  let U₁ := F₁.fixingSubgroup.comap r
  haveI : Finite (G ⧸ U₁) := Subgroup.finite_quotient_of_finiteIndex

  obtain ⟨F₂, hF₂, h₂⟩ := exists_level_forall_of_finite hsm (fun a : G ⧸ U₁ => y a.out)
  haveI := hF₂
  obtain ⟨F, hF, hG, hle⟩ := exists_isGalois_ge (F₁ ⊔ F₂)
  refine ⟨F, hF, hG, fun g s hs => h₁ g s (fixingSubgroup_antitone (le_sup_left.trans hle) hs),
    fun g s hs => ?_⟩
  obtain ⟨u, hu, hgu⟩ := out_coe_eq U₁ g
  have hyg : y ((g : G ⧸ U₁).out) = y g := by rw [hgu]; exact (h₁ g u hu).1
  rw [← hyg]
  exact h₂ (g : G ⧸ U₁) s (fixingSubgroup_antitone (le_sup_right.trans hle) hs)

theorem exists_level₂ {x : G × G → M} (hx : IsLevelConstant₂ r x) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      (∀ g g' s : G, r s ∈ F.fixingSubgroup →
        x (g * s, g') = x (g, g') ∧ x (s * g, g') = x (g, g') ∧
        x (g, g' * s) = x (g, g') ∧ x (g, s * g') = x (g, g')) ∧
      (∀ g g' s : G, r s ∈ F.fixingSubgroup → M.ρ s (x (g, g')) = x (g, g')) := by
  obtain ⟨F₁, hF₁, hG₁, h₁⟩ := lc₂ hx
  haveI := hF₁; haveI := hG₁
  let U₁ := F₁.fixingSubgroup.comap r
  haveI : Finite (G ⧸ U₁) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨F₂, hF₂, h₂⟩ :=
    exists_level_forall_of_finite hsm (fun p : (G ⧸ U₁) × (G ⧸ U₁) => x (p.1.out, p.2.out))
  haveI := hF₂
  obtain ⟨F, hF, hG, hle⟩ := exists_isGalois_ge (F₁ ⊔ F₂)
  refine ⟨F, hF, hG, fun g g' s hs => h₁ g g' s (fixingSubgroup_antitone (le_sup_left.trans hle) hs),
    fun g g' s hs => ?_⟩
  obtain ⟨u, hu, hgu⟩ := out_coe_eq U₁ g
  obtain ⟨u', hu', hgu'⟩ := out_coe_eq U₁ g'
  have hxg : x ((g : G ⧸ U₁).out, (g' : G ⧸ U₁).out) = x (g, g') := by
    rw [hgu, hgu', (h₁ g _ u hu).1, (h₁ g g' u' hu').2.2.1]
  rw [← hxg]
  exact h₂ ((g : G ⧸ U₁), (g' : G ⧸ U₁)) s (fixingSubgroup_antitone (le_sup_right.trans hle) hs)

end smooth

section qti

variable {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (U : Subgroup G) [U.Normal]

theorem qti_ρ_coe (g : G) (v : M.quotientToInvariants U) :
    (((M.quotientToInvariants U).ρ (g : G ⧸ U) v : M.quotientToInvariants U) : M) = M.ρ g (v : M) :=
  rfl

omit [U.Normal] in
theorem coe_eq_of_mem {g s : G} (hs : s ∈ U) : ((g * s : G) : G ⧸ U) = (g : G ⧸ U) := by
  rw [QuotientGroup.eq]; simpa using U.inv_mem hs

theorem qti_ρ_coe' (g : G) (v : M.quotientToInvariants U) :
    (((M.ρ.quotientToInvariants U) (g : G ⧸ U) v : M.quotientToInvariants U) : M) = M.ρ g (v : M) :=
  rfl

end qti

end P2mS26U5

open groupCohomology in
theorem solution {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G)
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k S) (b : S × S → N) (hb : b ∈ groupCohomology.levelCocycles₂ (r.comp S.subtype) N) :
    ∃ c : G × G → Rep.coind S.subtype N, c ∈ groupCohomology.levelCocycles₂ r (Rep.coind S.subtype N) ∧
      ∀ s s' : S, ((c ((s : G), (s' : G)) : Rep.coind S.subtype N) : G → N) 1 = b (s, s') := by
  classical

  let rep₀ : G → G := fun g => (Quotient.mk (QuotientGroup.rightRel S) g).out
  have rep₀_spec : ∀ g : G, g * (rep₀ g)⁻¹ ∈ S := fun g =>
    QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel S) g)
  have rep₀_mul : ∀ (s : G) (_ : s ∈ S) (g : G), rep₀ (s * g) = rep₀ g := fun s hs g => by
    show (Quotient.mk _ (s * g)).out = (Quotient.mk _ g).out
    congr 1
    apply Quotient.sound
    show @Setoid.r _ (QuotientGroup.rightRel S) (s * g) g
    rw [QuotientGroup.rightRel_apply]; simpa using hs
  have h1S : rep₀ 1 ∈ S := by simpa using rep₀_spec 1
  let rep : G → G := fun g => (rep₀ 1)⁻¹ * rep₀ g
  have rep_spec : ∀ g : G, g * (rep g)⁻¹ ∈ S := fun g => by
    show g * ((rep₀ 1)⁻¹ * rep₀ g)⁻¹ ∈ S
    rw [mul_inv_rev, inv_inv, ← mul_assoc]
    exact S.mul_mem (rep₀_spec g) h1S
  have rep_mul : ∀ (s : G) (_ : s ∈ S) (g : G), rep (s * g) = rep g := fun s hs g => by
    show (rep₀ 1)⁻¹ * rep₀ (s * g) = (rep₀ 1)⁻¹ * rep₀ g
    rw [rep₀_mul s hs g]
  have rep_one : rep 1 = 1 := by show (rep₀ 1)⁻¹ * rep₀ 1 = 1; exact inv_mul_cancel _
  let σ : G → S := fun x => ⟨x * (rep x)⁻¹, rep_spec x⟩
  have σ_mul : ∀ (s : S) (x : G), σ ((s : G) * x) = s * σ x := fun s x => by
    apply Subtype.ext
    show (s : G) * x * (rep ((s : G) * x))⁻¹ = s * (x * (rep x)⁻¹)
    rw [rep_mul _ s.2, mul_assoc]
  have σ_one : σ 1 = 1 := by apply Subtype.ext; show 1 * (rep 1)⁻¹ = 1; rw [rep_one]; simp
  have σ_S : ∀ s : S, σ s = s := fun s => by rw [← mul_one (s : G), σ_mul, σ_one, mul_one]

  let cfun : G → G → G → N := fun g h x =>
    N.ρ (σ x) (b ((σ x)⁻¹ * σ (x * g), (σ (x * g))⁻¹ * σ (x * g * h)))
  have cmem : ∀ g h, cfun g h ∈ Representation.coindV S.subtype N.ρ := fun g h s x => by
    show N.ρ (σ ((s : G) * x)) (b ((σ ((s : G) * x))⁻¹ * σ ((s : G) * x * g), (σ ((s : G) * x * g))⁻¹ * σ ((s : G) * x * g * h)))
      = N.ρ s (N.ρ (σ x) (b ((σ x)⁻¹ * σ (x * g), (σ (x * g))⁻¹ * σ (x * g * h))))
    rw [mul_assoc (s : G) x g, mul_assoc (s : G) (x * g) h, σ_mul, σ_mul, σ_mul, mul_inv_rev, mul_inv_rev,
      mul_assoc (σ x)⁻¹ s⁻¹, inv_mul_cancel_left, mul_assoc (σ (x * g))⁻¹ s⁻¹, inv_mul_cancel_left,
      map_mul, Module.End.mul_apply]
  let c : G × G → Rep.coind S.subtype N := fun p => ⟨cfun p.1 p.2, cmem p.1 p.2⟩
  have c_apply : ∀ g h x, ((c (g, h) : Rep.coind S.subtype N) : G → N) x
      = N.ρ (σ x) (b ((σ x)⁻¹ * σ (x * g), (σ (x * g))⁻¹ * σ (x * g * h))) := fun _ _ _ => rfl
  have hcoc : c ∈ cocycles₂ (Rep.coind S.subtype N) := by
    rw [mem_cocycles₂_iff]
    intro g h j
    apply Subtype.ext
    funext x
    show ((c (g * h, j) : Rep.coind S.subtype N) : G → N) x + ((c (g, h) : Rep.coind S.subtype N) : G → N) x
      = ((c (h, j) : Rep.coind S.subtype N) : G → N) (x * g) + ((c (g, h * j) : Rep.coind S.subtype N) : G → N) x
    rw [c_apply, c_apply, c_apply, c_apply, ← mul_assoc x g h, ← mul_assoc (x * g) h j]
    have e1 : (σ x)⁻¹ * σ (x * g * h) = ((σ x)⁻¹ * σ (x * g)) * ((σ (x * g))⁻¹ * σ (x * g * h)) := by group
    have e2 : (σ (x * g))⁻¹ * σ (x * g * h * j)
        = ((σ (x * g))⁻¹ * σ (x * g * h)) * ((σ (x * g * h))⁻¹ * σ (x * g * h * j)) := by group
    rw [e1, e2, ← map_add, (mem_cocycles₂_iff b).1 hb.1, map_add, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel_left]
  have hev : ∀ s s' : S, ((c ((s : G), (s' : G)) : Rep.coind S.subtype N) : G → N) 1 = b (s, s') := by
    intro s s'
    rw [c_apply, one_mul, ← Subgroup.coe_mul, σ_one, σ_S, σ_S, inv_one, one_mul, inv_mul_cancel_left, map_one,
      Module.End.one_apply]

  obtain ⟨F₀, hF₀, hle₀⟩ := hS
  obtain ⟨Fb, hFb, hGb, hinv⟩ := P2mS26U5.lc₂ hb.2
  haveI := hF₀; haveI := hFb
  obtain ⟨F, hF, hG, hle⟩ := P2mS26U5.exists_isGalois_ge (F₀ ⊔ Fb)
  haveI := hF; haveI := hG
  have hN : (F.fixingSubgroup.comap r).Normal := inferInstance
  have hUS : F.fixingSubgroup.comap r ≤ S :=
    (Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hle))).trans hle₀
  have hUb : ∀ (v : G) (hv : v ∈ F.fixingSubgroup.comap r), (r.comp S.subtype) ⟨v, hUS hv⟩ ∈ Fb.fixingSubgroup :=
    fun v hv => IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hle) hv
  refine ⟨c, ⟨hcoc, F, hF, fun g h u u' hu hu' => ?_⟩, hev⟩
  apply Subtype.ext
  funext x
  show ((c (g * u, h * u') : Rep.coind S.subtype N) : G → N) x = ((c (g, h) : Rep.coind S.subtype N) : G → N) x
  rw [c_apply, c_apply]

  have hu₁ : rep (x * g) * u * (rep (x * g))⁻¹ ∈ F.fixingSubgroup.comap r := hN.conj_mem u hu _
  have hw : h⁻¹ * u * h * u' ∈ F.fixingSubgroup.comap r :=
    Subgroup.mul_mem _ (by simpa using hN.conj_mem u hu h⁻¹) hu'
  have hu₃ : rep (x * g * h) * (h⁻¹ * u * h * u') * (rep (x * g * h))⁻¹ ∈ F.fixingSubgroup.comap r :=
    hN.conj_mem _ hw _
  have hrep1 : rep (x * (g * u)) = rep (x * g) := by
    rw [show x * (g * u) = (x * g * u * (x * g)⁻¹) * (x * g) by group,
      rep_mul _ (hUS (hN.conj_mem u hu (x * g)))]
  have hrep2 : rep (x * (g * u) * (h * u')) = rep (x * g * h) := by
    rw [show x * (g * u) * (h * u') = (x * g * h * (h⁻¹ * u * h * u') * (x * g * h)⁻¹) * (x * g * h) by group,
      rep_mul _ (hUS (hN.conj_mem _ hw (x * g * h)))]
  set u₁ : S := ⟨_, hUS hu₁⟩ with hu₁def
  set u₃ : S := ⟨_, hUS hu₃⟩ with hu₃def
  have h1 : (r.comp S.subtype) u₁ ∈ Fb.fixingSubgroup := hUb _ hu₁
  have h3 : (r.comp S.subtype) u₃ ∈ Fb.fixingSubgroup := hUb _ hu₃
  have e1 : σ (x * (g * u)) = σ (x * g) * u₁ := by
    apply Subtype.ext
    show x * (g * u) * (rep (x * (g * u)))⁻¹ = x * g * (rep (x * g))⁻¹ * (rep (x * g) * u * (rep (x * g))⁻¹)
    rw [hrep1]; group
  have e2 : σ (x * (g * u) * (h * u')) = σ (x * g * h) * u₃ := by
    apply Subtype.ext
    show x * (g * u) * (h * u') * (rep (x * (g * u) * (h * u')))⁻¹
      = x * g * h * (rep (x * g * h))⁻¹ * (rep (x * g * h) * (h⁻¹ * u * h * u') * (rep (x * g * h))⁻¹)
    rw [hrep2]; group
  have e3 : (σ x)⁻¹ * (σ (x * g) * u₁) = ((σ x)⁻¹ * σ (x * g)) * u₁ := by group
  have e4 : (σ (x * g) * u₁)⁻¹ * (σ (x * g * h) * u₃) = u₁⁻¹ * (((σ (x * g))⁻¹ * σ (x * g * h)) * u₃) := by group
  have h1' : (r.comp S.subtype) u₁⁻¹ ∈ Fb.fixingSubgroup := by rw [map_inv]; exact Subgroup.inv_mem _ h1
  rw [e1, e2, e3, e4, (hinv _ _ u₁ h1).1, (hinv _ _ u₁⁻¹ h1').2.2.2, (hinv _ _ u₃ h3).2.2.1]

end S_groupCohomology_exists_coind_mem_levelCocycles2_eval_one_eq
end P2MW
export P2MW.S_groupCohomology_exists_coind_mem_levelCocycles2_eval_one_eq (solution)
