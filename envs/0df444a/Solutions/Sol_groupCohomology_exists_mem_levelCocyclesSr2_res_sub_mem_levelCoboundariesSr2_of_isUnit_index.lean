-- Prove2me | solution 1 for groupCohomology.exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/419ed922-4f94-5b90-b212-ef1fd69852db

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

namespace P2MCorSr2

local instance isAlgebraicQbar_corSr2 : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_corSr2 : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_corSr2 : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

variable {k G : Type u} [CommRing k] [Group G] (N : Subgroup G)

noncomputable def sec (c : G ⧸ N) : G := Quotient.out c

@[scoped simp] lemma mk_sec (c : G ⧸ N) : (QuotientGroup.mk (sec N c) : G ⧸ N) = c := QuotientGroup.out_eq' c

variable [N.Normal]

lemma sec_mul_mul_inv_mem (c : G ⧸ N) (g : G) : sec N c * g * (sec N (c * (g : G ⧸ N)))⁻¹ ∈ N := by
  rw [← QuotientGroup.eq_one_iff]
  simp

noncomputable def nn (c : G ⧸ N) (g : G) : ↥N := ⟨_, sec_mul_mul_inv_mem N c g⟩

@[scoped simp] lemma coe_nn (c : G ⧸ N) (g : G) :
    (nn N c g : G) = sec N c * g * (sec N (c * (g : G ⧸ N)))⁻¹ := rfl

lemma nn_mul (c : G ⧸ N) (g h : G) : nn N c (g * h) = nn N c g * nn N (c * (g : G ⧸ N)) h := by
  ext
  simp [mul_assoc]

lemma mk_mul_of_mem (c : G ⧸ N) {a : G} (ha : a ∈ N) : c * (a : G ⧸ N) = c := by
  rw [(QuotientGroup.eq_one_iff a).2 ha, mul_one]

lemma coe_nn_of_mem (c : G ⧸ N) {a : G} (ha : a ∈ N) : (nn N c a : G) = sec N c * a * (sec N c)⁻¹ := by
  simp [mk_mul_of_mem N c ha]

lemma inv_sec_mul_nn (c : G ⧸ N) (g : G) : (sec N c)⁻¹ * (nn N c g : G) = g * (sec N (c * (g : G ⧸ N)))⁻¹ := by
  simp [mul_assoc]

variable [Fintype (G ⧸ N)] (M : Rep.{u} k G)

noncomputable def cor (f : ↥N × ↥N → M) : G × G → M := fun gh =>
  ∑ c : G ⧸ N, M.ρ (sec N c)⁻¹ (f (nn N c gh.1, nn N (c * (gh.1 : G ⧸ N)) gh.2))

lemma cor_apply (f : ↥N × ↥N → M) (g h : G) :
    cor N M f (g, h) = ∑ c : G ⧸ N, M.ρ (sec N c)⁻¹ (f (nn N c g, nn N (c * (g : G ⧸ N)) h)) := rfl

lemma ρ_mul_apply (g h : G) (m : M) : M.ρ g (M.ρ h m) = M.ρ (g * h) m := by
  rw [map_mul]; rfl

lemma cor_mem_cocycles₂ {f : ↥N × ↥N → M} (hf : f ∈ cocycles₂ (Rep.res N.subtype M)) :
    cor N M f ∈ cocycles₂ M := by
  rw [mem_cocycles₂_def] at hf ⊢
  intro g h j
  have key : M.ρ g (cor N M f (h, j)) = ∑ c : G ⧸ N, M.ρ (sec N c)⁻¹
      (M.ρ (nn N c g : G) (f (nn N (c * (g : G ⧸ N)) h, nn N (c * (g : G ⧸ N) * (h : G ⧸ N)) j))) := by
    rw [cor_apply, map_sum, ← Equiv.sum_comp (Equiv.mulRight (g : G ⧸ N))]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Equiv.coe_mulRight]
    rw [ρ_mul_apply, ρ_mul_apply, inv_sec_mul_nn]
  rw [key, cor_apply, cor_apply, cor_apply, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun c _ => ?_
  have e1 : (c * ((g * h : G) : G ⧸ N)) = c * (g : G ⧸ N) * (h : G ⧸ N) := by
    rw [QuotientGroup.mk_mul, mul_assoc]
  rw [← map_sub, ← map_add, ← map_sub, nn_mul N c g h, e1, nn_mul N (c * (g : G ⧸ N)) h j]
  have := hf (nn N c g) (nn N (c * (g : G ⧸ N)) h) (nn N (c * (g : G ⧸ N) * (h : G ⧸ N)) j)
  rw [Rep.coe_res_obj_ρ', Subgroup.subtype_apply] at this
  rw [this, map_zero]

lemma cor_apply_coe (f : ↥N × ↥N → M) (a b : ↥N) :
    cor N M f ((a : G), (b : G)) = ∑ c : G ⧸ N, M.ρ (sec N c)⁻¹
      (f (MulAut.conjNormal ((sec N c)⁻¹)⁻¹ a, MulAut.conjNormal ((sec N c)⁻¹)⁻¹ b)) := by
  rw [cor_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  have ha : nn N c a = MulAut.conjNormal ((sec N c)⁻¹)⁻¹ a := by
    ext; rw [coe_nn_of_mem N c a.2, MulAut.conjNormal_apply, inv_inv]
  have hb : nn N (c * ((a : G) : G ⧸ N)) b = MulAut.conjNormal ((sec N c)⁻¹)⁻¹ b := by
    ext; rw [mk_mul_of_mem N c a.2, coe_nn_of_mem N c b.2, MulAut.conjNormal_apply, inv_inv]
  rw [ha, hb]

section level

variable (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)

lemma exists_normal_level {F F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)} (hF : F.IsUnramifiedOutside S)
    (hF₀ : F₀.IsUnramifiedOutside S) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), E.IsUnramifiedOutside S ∧ (E.fixingSubgroup.comap r).Normal ∧
      F ≤ E ∧ F₀ ≤ E := by
  haveI := (hF.sup hF₀).1
  haveI : Normal ℚ (IntermediateField.normalClosure ℚ (↥(F ⊔ F₀)) (AlgebraicClosure ℚ)) := by
    have := normalClosure.normal ℚ (↥(F ⊔ F₀)) (AlgebraicClosure ℚ); convert this <;> first | rfl | exact Subsingleton.elim _ _
  exact ⟨IntermediateField.normalClosure ℚ (↥(F ⊔ F₀)) (AlgebraicClosure ℚ), (hF.sup hF₀).normalClosure,
    groupCohomology.normal_comap_fixingSubgroup r _,
    le_sup_left.trans (IntermediateField.le_normalClosure (F ⊔ F₀)),
    le_sup_right.trans (IntermediateField.le_normalClosure (F ⊔ F₀))⟩

lemma cor_isLevelConstantSr₂ {f : ↥N × ↥N → M} (hf : IsLevelConstantSr₂ (r.comp N.subtype) S f)
    (hN : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), F₀.IsUnramifiedOutside S ∧ F₀.fixingSubgroup.comap r ≤ N) :
    IsLevelConstantSr₂ r S (cor N M f) := by
  obtain ⟨F, hF, hcf⟩ := hf
  obtain ⟨F₀, hF₀, hle⟩ := hN
  obtain ⟨E, hE, hEn, hFE, hF₀E⟩ := exists_normal_level r S hF hF₀
  have hEN : E.fixingSubgroup.comap r ≤ N := (comap_fixingSubgroup_antitone r hF₀E).trans hle
  have hEF : E.fixingSubgroup ≤ F.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hFE
  refine ⟨E, hE, fun g g' s s' hs hs' => ?_⟩
  have hsN : s ∈ N := hEN hs
  have hs'N : s' ∈ N := hEN hs'
  rw [cor_apply, cor_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : c * ((g * s : G) : G ⧸ N) = c * (g : G ⧸ N) := by
    rw [QuotientGroup.mk_mul, ← mul_assoc, mk_mul_of_mem N _ hsN]
  rw [nn_mul, e1, nn_mul]

  have h1 : (r.comp N.subtype) (nn N (c * (g : G ⧸ N)) s) ∈ F.fixingSubgroup := by
    refine hEF ?_
    have := hEn.conj_mem s hs (sec N (c * (g : G ⧸ N)))
    rw [Subgroup.mem_comap] at this
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, coe_nn_of_mem N _ hsN]
    exact this
  have h2 : (r.comp N.subtype) (nn N (c * (g : G ⧸ N) * (g' : G ⧸ N)) s') ∈ F.fixingSubgroup := by
    refine hEF ?_
    have := hEn.conj_mem s' hs' (sec N (c * (g : G ⧸ N) * (g' : G ⧸ N)))
    rw [Subgroup.mem_comap] at this
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, coe_nn_of_mem N _ hs'N]
    exact this
  rw [hcf _ _ _ _ h1 h2]

end level

lemma res_cor_sub (x : ↥N × ↥N → M) :
    (fun ab : ↥N × ↥N => cor N M x ((ab.1 : G), (ab.2 : G))) - (Fintype.card (G ⧸ N) : k) • x =
      ∑ c : G ⧸ N, ((fun ab : ↥N × ↥N => M.ρ (sec N c)⁻¹
        (x (MulAut.conjNormal ((sec N c)⁻¹)⁻¹ ab.1, MulAut.conjNormal ((sec N c)⁻¹)⁻¹ ab.2))) - x) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  congr 1
  funext ab
  rw [Finset.sum_apply, cor_apply_coe]

end P2MCorSr2
p2m_reactivate "P2MW.S_groupCohomology_exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index.P2MCorSr2"

open P2MCorSr2 in
theorem solution
    {k G : Type u} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (S : Finset Nat.Primes) (M : Rep.{u} k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g : G, r g ∈ F.fixingSubgroup → M.ρ g m = m)
    (N : Subgroup G) [N.Normal] [N.FiniteIndex] (hu : IsUnit ((N.index : ℕ) : k))
    (hN : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), F₀.IsUnramifiedOutside S ∧ F₀.fixingSubgroup.comap r ≤ N)
    (x : ↥N × ↥N → M) (hx : x ∈ levelCocyclesSr₂ (r.comp N.subtype) S (Rep.res N.subtype M))
    (hinv : ∀ g : G,
      (fun ab : ↥N × ↥N => M.ρ g (x (MulAut.conjNormal g⁻¹ ab.1, MulAut.conjNormal g⁻¹ ab.2))) - x ∈
        levelCoboundariesSr₂ (r.comp N.subtype) S (Rep.res N.subtype M)) :
    ∃ y : G × G → M, y ∈ levelCocyclesSr₂ r S M ∧
      (fun ab : ↥N × ↥N => y ((ab.1 : G), (ab.2 : G))) - x ∈ levelCoboundariesSr₂ (r.comp N.subtype) S (Rep.res N.subtype M) := by
  classical
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _

  have hcard : (Fintype.card (G ⧸ N) : k) = (N.index : k) := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  set u : kˣ := hu.unit
  have hu' : ((u : k)) = (Fintype.card (G ⧸ N) : k) := by rw [hcard]; rfl

  refine ⟨((u⁻¹ : kˣ) : k) • cor N M x, Submodule.smul_mem _ _ ⟨cor_mem_cocycles₂ N M hx.1,
    cor_isLevelConstantSr₂ N M r S hx.2 hN⟩, ?_⟩

  have hxeq : x = ((u⁻¹ : kˣ) : k) • ((Fintype.card (G ⧸ N) : k) • x) := by
    rw [← hu', smul_smul, Units.inv_mul, one_smul]
  have : (fun ab : ↥N × ↥N => (((u⁻¹ : kˣ) : k) • cor N M x) ((ab.1 : G), (ab.2 : G))) - x =
      ((u⁻¹ : kˣ) : k) • ((fun ab : ↥N × ↥N => cor N M x ((ab.1 : G), (ab.2 : G))) -
        (Fintype.card (G ⧸ N) : k) • x) := by
    rw [smul_sub, ← hxeq]
    rfl
  rw [this, res_cor_sub]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun c _ => hinv (sec N c)⁻¹)

end S_groupCohomology_exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index
end P2MW
export P2MW.S_groupCohomology_exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index (solution)
