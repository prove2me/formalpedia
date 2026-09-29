-- Prove2me | solution 1 for groupCohomology.coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/bf414e7a-ce4b-5b22-9210-b5ff7669c49d

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2

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
    (N : Rep.{u} k S) (c : G × G → Rep.coind S.subtype N)
    (hc : c ∈ groupCohomology.levelCocycles₂ r (Rep.coind S.subtype N))
    (h : (fun p : S × S => ((c ((p.1 : G), (p.2 : G)) : Rep.coind S.subtype N) : G → N) 1)
      ∈ groupCohomology.levelCoboundaries₂ (r.comp S.subtype) N) :
    c ∈ groupCohomology.levelCoboundaries₂ r (Rep.coind S.subtype N) := by
  classical

  let rep : G → G := fun g => (Quotient.mk (QuotientGroup.rightRel S) g).out
  have rep_spec : ∀ g : G, g * (rep g)⁻¹ ∈ S := fun g =>
    QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel S) g)
  have rep_mul : ∀ (s : G) (_ : s ∈ S) (g : G), rep (s * g) = rep g := fun s hs g => by
    show (Quotient.mk _ (s * g)).out = (Quotient.mk _ g).out
    congr 1
    apply Quotient.sound
    show @Setoid.r _ (QuotientGroup.rightRel S) (s * g) g
    rw [QuotientGroup.rightRel_apply]; simpa using hs
  let σ : G → S := fun x => ⟨x * (rep x)⁻¹, rep_spec x⟩
  have hx : ∀ x : G, x = (σ x : G) * rep x := fun x => by simp [σ]
  have σ_mul : ∀ (s : S) (x : G), σ ((s : G) * x) = s * σ x := fun s x => by
    apply Subtype.ext
    show (s : G) * x * (rep ((s : G) * x))⁻¹ = s * (x * (rep x)⁻¹)
    rw [rep_mul _ s.2, mul_assoc]

  let K : G → G → N := fun y z => ((c (y, z) : Rep.coind S.subtype N) : G → N) 1
  have Kdef : ∀ y z, ((c (y, z) : Rep.coind S.subtype N) : G → N) 1 = K y z := fun _ _ => rfl
  have E0 : ∀ g h' x, ((c (g, h') : Rep.coind S.subtype N) : G → N) x = K (x * g) h' + K x g - K x (g * h') := by
    intro g h' x
    have hh := (mem_cocycles₂_iff c).1 hc.1 x g h'
    have := congrArg (fun f : Rep.coind S.subtype N => (f : G → N) 1) hh
    simp only [Submodule.coe_add] at this
    rw [Pi.add_apply, Pi.add_apply] at this
    have e : (((Rep.coind S.subtype N).ρ x (c (g, h')) : Rep.coind S.subtype N) : G → N) 1
        = ((c (g, h') : Rep.coind S.subtype N) : G → N) x := by
      show ((c (g, h') : Rep.coind S.subtype N) : G → N) (1 * x) = _; rw [one_mul]
    rw [e] at this
    rw [Kdef, Kdef, Kdef] at this
    exact eq_sub_of_add_eq this.symm
  have ES : ∀ (s : S) (y z : G), ((c (y, z) : Rep.coind S.subtype N) : G → N) s = N.ρ s (K y z) := by
    intro s y z
    rw [← Kdef, ← mul_one (s : G)]
    exact (c (y, z) : Rep.coind S.subtype N).2 s 1
  have Kcongr : ∀ {y z y' z' : G}, c (y, z) = c (y', z') → K y z = K y' z' := fun hyz => by
    rw [← Kdef, ← Kdef, hyz]
  have E1 : ∀ (s : S) (y z : G), K ((s : G) * y) z = N.ρ s (K y z) + K s (y * z) - K s y := by
    intro s y z
    have := E0 y z s
    rw [ES] at this
    rw [this]; abel

  obtain ⟨e, he_lc, he⟩ := (mem_levelCoboundaries₂_iff (r.comp S.subtype) N _).1 h
  have E7 : ∀ α β : S, K α β = N.ρ α (e β) - e (α * β) + e α := by
    intro α β
    have := congrFun he (α, β)
    rw [d₁₂_hom_apply] at this
    dsimp only at this
    rw [← Kdef]
    exact this.symm

  let Ffun : G → G → N := fun g x =>
    N.ρ (σ x) (K (rep x) g - K ((σ x)⁻¹ * σ (x * g) : S) (rep (x * g)) + e ((σ x)⁻¹ * σ (x * g)))
  have Fmem : ∀ g, Ffun g ∈ Representation.coindV S.subtype N.ρ := fun g s x => by
    show N.ρ (σ ((s : G) * x)) (K (rep ((s : G) * x)) g - K ((σ ((s : G) * x))⁻¹ * σ ((s : G) * x * g) : S)
        (rep ((s : G) * x * g)) + e ((σ ((s : G) * x))⁻¹ * σ ((s : G) * x * g)))
      = N.ρ s (N.ρ (σ x) (K (rep x) g - K ((σ x)⁻¹ * σ (x * g) : S) (rep (x * g)) + e ((σ x)⁻¹ * σ (x * g))))
    rw [mul_assoc (s : G) x g, rep_mul _ s.2, rep_mul _ s.2, σ_mul, σ_mul, mul_inv_rev, mul_assoc (σ x)⁻¹ s⁻¹,
      inv_mul_cancel_left, map_mul, Module.End.mul_apply]
  let F₁ : G → Rep.coind S.subtype N := fun g => ⟨Ffun g, Fmem g⟩
  have F_apply : ∀ g x, ((F₁ g : Rep.coind S.subtype N) : G → N) x
      = N.ρ (σ x) (K (rep x) g - K ((σ x)⁻¹ * σ (x * g) : S) (rep (x * g)) + e ((σ x)⁻¹ * σ (x * g))) :=
    fun _ _ => rfl

  obtain ⟨F₀, hF₀, hle₀⟩ := hS
  obtain ⟨Fc, hFc, hGc, hcinv⟩ := P2mS26U5.lc₂ hc.2
  obtain ⟨Fe, hFe, hFe'⟩ := he_lc
  haveI := hF₀; haveI := hFc; haveI := hFe
  obtain ⟨F, hF, hG, hle⟩ := P2mS26U5.exists_isGalois_ge (F₀ ⊔ Fc ⊔ Fe)
  haveI := hF; haveI := hG
  have hN : (F.fixingSubgroup.comap r).Normal := inferInstance
  have hUS : F.fixingSubgroup.comap r ≤ S :=
    (Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone
      ((le_sup_left.trans le_sup_left).trans hle))).trans hle₀
  have F_lc : IsLevelConstant₁ r F₁ := by
    refine ⟨F, hF, fun g u hu => ?_⟩
    apply Subtype.ext
    funext x
    rw [F_apply, F_apply]
    have hu₁ : rep (x * g) * u * (rep (x * g))⁻¹ ∈ F.fixingSubgroup.comap r := hN.conj_mem u hu _
    have hrep : rep (x * (g * u)) = rep (x * g) := by
      rw [show x * (g * u) = (x * g * u * (x * g)⁻¹) * (x * g) by group,
        rep_mul _ (hUS (hN.conj_mem u hu (x * g)))]
    set u₁ : S := ⟨_, hUS hu₁⟩
    have e1 : σ (x * (g * u)) = σ (x * g) * u₁ := by
      apply Subtype.ext
      show x * (g * u) * (rep (x * (g * u)))⁻¹ = x * g * (rep (x * g))⁻¹ * (rep (x * g) * u * (rep (x * g))⁻¹)
      rw [hrep]; group
    have huc : r u ∈ Fc.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone ((le_sup_right.trans le_sup_left).trans hle) hu
    have hu₁c : r (u₁ : G) ∈ Fc.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone ((le_sup_right.trans le_sup_left).trans hle) hu₁
    have hu₁e : (r.comp S.subtype) u₁ ∈ Fe.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hle) hu₁
    rw [hrep, e1, Kcongr ((hcinv (rep x) g u huc).2.2.1), ← mul_assoc, Subgroup.coe_mul,
      Kcongr ((hcinv _ (rep (x * g)) (u₁ : G) hu₁c).1), hFe' _ u₁ hu₁e]

  refine (mem_levelCoboundaries₂_iff r _ _).2 ⟨F₁, F_lc, ?_⟩
  funext ⟨g, h'⟩
  apply Subtype.ext
  funext x
  rw [d₁₂_hom_apply]
  show ((F₁ h' : Rep.coind S.subtype N) : G → N) (x * g) - ((F₁ (g * h') : Rep.coind S.subtype N) : G → N) x
      + ((F₁ g : Rep.coind S.subtype N) : G → N) x = ((c (g, h') : Rep.coind S.subtype N) : G → N) x

  have hrepx : ∀ y : G, rep y = ((σ y : S) : G)⁻¹ * y := fun y => eq_inv_mul_iff_mul_eq.2 (hx y).symm
  have hgen : ∀ y z : G, rep y * z = (((σ y)⁻¹ * σ (y * z) : S) : G) * rep (y * z) := by
    intro y z
    rw [hrepx y, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc (((σ y : S) : G)⁻¹) ((σ (y * z) : S) : G),
      ← hx (y * z), mul_assoc]
  have htg : rep x * g = (((σ x)⁻¹ * σ (x * g) : S) : G) * rep (x * g) := hgen x g
  have ht1h : rep (x * g) * h' = (((σ (x * g))⁻¹ * σ (x * g * h') : S) : G) * rep (x * g * h') := hgen (x * g) h'
  have hAB : (σ x)⁻¹ * σ (x * g * h') = ((σ x)⁻¹ * σ (x * g)) * ((σ (x * g))⁻¹ * σ (x * g * h')) := by group
  have hσ1 : σ (x * g) = σ x * ((σ x)⁻¹ * σ (x * g)) := by group

  rw [F_apply, F_apply, F_apply, E0]
  rw [show x * (g * h') = x * g * h' from (mul_assoc x g h').symm, hAB]

  have K1 : K x g = N.ρ (σ x) (K (rep x) g) + K (σ x) (rep x * g) - K (σ x) (rep x) := by
    conv_lhs => rw [hx x]
    exact E1 _ _ _
  have K2 : K x (g * h') = N.ρ (σ x) (K (rep x) (g * h')) + K (σ x) (rep x * (g * h')) - K (σ x) (rep x) := by
    conv_lhs => rw [hx x]
    exact E1 _ _ _
  have K3 : K (x * g) h' = N.ρ (σ (x * g)) (K (rep (x * g)) h') + K (σ (x * g)) (rep (x * g) * h')
      - K (σ (x * g)) (rep (x * g)) := by
    conv_lhs => rw [hx (x * g)]
    exact E1 _ _ _
  have K4 : ∀ w, K (σ (x * g)) w = N.ρ (σ x) (K ((σ x)⁻¹ * σ (x * g) : S) w)
      + K (σ x) ((((σ x)⁻¹ * σ (x * g) : S) : G) * w) - K (σ x) ((σ x)⁻¹ * σ (x * g) : S) := by
    intro w
    conv_lhs => rw [hσ1, Subgroup.coe_mul]
    exact E1 _ _ _
  have K6 : K ((((σ x)⁻¹ * σ (x * g)) * ((σ (x * g))⁻¹ * σ (x * g * h')) : S) : G) (rep (x * g * h'))
      = N.ρ ((σ x)⁻¹ * σ (x * g) : S) (K ((σ (x * g))⁻¹ * σ (x * g * h') : S) (rep (x * g * h')))
        + K ((σ x)⁻¹ * σ (x * g) : S) ((((σ (x * g))⁻¹ * σ (x * g * h') : S) : G) * rep (x * g * h'))
        - K ((σ x)⁻¹ * σ (x * g) : S) ((σ (x * g))⁻¹ * σ (x * g * h') : S) := by
    rw [Subgroup.coe_mul]
    exact E1 _ _ _
  have hρ1 : N.ρ (σ (x * g)) = N.ρ (σ x) * N.ρ ((σ x)⁻¹ * σ (x * g)) := by
    rw [← map_mul, mul_inv_cancel_left]
  have hw1 : (((σ x)⁻¹ * σ (x * g) : S) : G) * (rep (x * g) * h') = rep x * (g * h') := by
    rw [← mul_assoc, ← htg, mul_assoc]
  have hw2 : (((σ (x * g))⁻¹ * σ (x * g * h') : S) : G) * rep (x * g * h') = rep (x * g) * h' := ht1h.symm
  have hw3 : (((σ x)⁻¹ * σ (x * g) : S) : G) * rep (x * g) = rep x * g := htg.symm
  rw [K1, K2, K3, K4, K4, K6, E7 ((σ x)⁻¹ * σ (x * g)) ((σ (x * g))⁻¹ * σ (x * g * h')), hρ1, hw2, hw1, hw3]
  simp only [map_add, map_sub, Module.End.mul_apply]
  abel

end S_groupCohomology_coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2
end P2MW
export P2MW.S_groupCohomology_coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2 (solution)
