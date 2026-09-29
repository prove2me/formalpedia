-- Prove2me | solution 1 for mme_stothers_phi125_finite_power_block_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T21:00:21.82522+00:00
-- url     : https://prove2.me/submissions/020f8124-8df5-4268-9ff7-da0f8072f2b8

import Definitions.Def_mme_CW_fourth_literal_support_words
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi116_fine_blocks
import Definitions.Def_mme_stothers_phi125_cyclic_hash_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Mathlib
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Tactic
import Theorems.Thm_mme_CW_fourth_tensor_eq_sum_literal_terms
import Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_MMObj_cyclic_tau_value
import Theorems.Thm_mme_ZMod_prime_affine_joint_fintype_card_le
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_fintype_card
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_cyclicSymmetrization_isomorphic_cyclic_orbit
import Theorems.Thm_mme_cyclic_grading_address_block_iso
import Theorems.Thm_mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
import Theorems.Thm_mme_cyclic_kron_two_strict_below_product
import Theorems.Thm_mme_cyclic_triple_grading_nonzero_factors
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso
import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree
import Theorems.Thm_mme_stothers_phi125_cyclic_affine_hash_AP
import Theorems.Thm_mme_stothers_phi125_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_stothers_phi125_cyclic_mode_fiber_card
import Theorems.Thm_mme_stothers_phi125_cyclic_mode_word_tuple_injective
import Theorems.Thm_mme_stothers_phi125_distinct_mode_code_difference_has_nonzero_coefficient
import Theorems.Thm_mme_stothers_phi125_exact_iff_marginal_profile
import Theorems.Thm_mme_stothers_phi125_exact_profile_card
import Theorems.Thm_mme_stothers_phi125_fine_component_restrictions
import Theorems.Thm_mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
import Theorems.Thm_mme_stothers_phi125_square_support_pair_classification
import Theorems.Thm_mme_stothers_phi233_lower_half_cast_label_package
import Theorems.Thm_mme_type2_fractional_retention_of_relative_mode_degree

/- Provenance: current-environment direct closure of the earlier phi125 proof
chain.  It replaces the old target proof's mutual dependency through profile
extraction with an explicit finite block construction. -/

universe u

set_option warningAsError true
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

section
open MME Module


namespace MME.StothersFourth.Phi125

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- The fixed coarse grade of the three mode spaces of `phi_125`. -/
def modeTotalGrade (s : Fin 3) : Fin 9 :=
  cwFourthBlockType 1 2 5 s

/-- Canonical fourth-power basis coordinates belonging to the coarse `(1,2,5)` constituent in one mode. -/
def ModeIndex (q : ℕ) (s : Fin 3) : Type :=
  {p : (Fin (q + 2) × Fin (q + 2)) × (Fin (q + 2) × Fin (q + 2)) //
    cwFourthPairGrade q p = modeTotalGrade s}

private theorem mode_span_eq
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Submodule.span K (Set.range (fun p : ModeIndex q s ↦ cwFourthCanonicalBasis K q s p.1)) =
      cwBasisGrade (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) (modeTotalGrade s) := by
  unfold cwBasisGrade
  congr 1
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

/-- Canonical basis of one mode of the literal coarse `phi_125` block. -/
noncomputable def canonicalBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis (ModeIndex q s) K ((cwFourthConstituent K q 1 2 5).V s) := by
  let b := cwFourthCanonicalBasis K q s
  let v : ModeIndex q s → (cwFourthObj K q).V s := fun p ↦ b p.1
  have hv : LinearIndependent K v := b.linearIndependent.comp _ Subtype.val_injective
  let bs := Basis.span hv
  have heq := mode_span_eq K q s
  let e : Submodule.span K (Set.range v) ≃ₗ[K]
      cwBasisGrade b (cwFourthPairGrade q) (modeTotalGrade s) := LinearEquiv.ofEq _ _ heq
  exact bs.map e

@[simp] theorem canonicalBasis_coe
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (p : ModeIndex q s) :
    (canonicalBasis K q s p).val = cwFourthCanonicalBasis K q s p.1 := by
  change
    (((Basis.span
      ((cwFourthCanonicalBasis K q s).linearIndependent.comp
        (fun p : ModeIndex q s => p.1) Subtype.val_injective)).map
      (LinearEquiv.ofEq _ _ (mode_span_eq K q s))) p).val =
      cwFourthCanonicalBasis K q s p.1
  rw [Basis.map_apply]
  change ((Basis.span _ p).val : (cwFourthObj K q).V s) = _
  exact Basis.coe_span_apply
    ((cwFourthCanonicalBasis K q s).linearIndependent.comp
      (fun p : ModeIndex q s => p.1) Subtype.val_injective) p

/-- The outer fine grade remembers the grade of the first square factor. -/
def outerGrade (q : ℕ) (s : Fin 3) (p : ModeIndex q s) : Fin 5 :=
  cwSquarePairGrade q p.1.1

/-- The literal five-grading of the actual coarse `phi_125` constituent. -/
noncomputable def outerGrading
    (K : Type u) [Field K] (q : ℕ) :
    (cwFourthConstituent K q 1 2 5).TypeGrading 5 where
  decomp s := cwBasisGrade (canonicalBasis K q s) (outerGrade q s)
  is_internal s := cwBasisGrade_isInternal (canonicalBasis K q s) (outerGrade q s)

end MME.StothersFourth.Phi125
end

section
open MME TensorProduct Module


namespace MME.StothersFourth.Phi125

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem p125_fb_canonical_basis_mem_grade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {iota kappa : Type*} [DecidableEq kappa]
    (b : Basis iota K V) (g : iota → kappa) (i : iota) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private theorem p125_fb_square_basis_mem_own_grade
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : Fin (q + 2) × Fin (q + 2)) :
    cwSquareCanonicalBasis K q s p ∈
      (cwSquareCanonicalGrading K q).classOf s
        (cwSquarePairGrade q p) := by
  exact Submodule.subset_span ⟨p, rfl, rfl⟩

private theorem p125_fb_fourth_basis_apply
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    cwFourthCanonicalBasis K q s p =
      cwSquareCanonicalBasis K q s p.1 ⊗ₜ[K]
        cwSquareCanonicalBasis K q s p.2 := by
  unfold cwFourthCanonicalBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

private theorem p125_fb_fourth_basis_mem_own_fine_grade
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    cwFourthCanonicalBasis K q s p ∈
      (TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).classOf s
          (finProdFinEquiv
            (cwSquarePairGrade q p.1, cwSquarePairGrade q p.2)) := by
  let G := cwSquareCanonicalGrading K q
  let z : G.classOf s (cwSquarePairGrade q p.1) ⊗[K]
      G.classOf s (cwSquarePairGrade q p.2) :=
    ⟨cwSquareCanonicalBasis K q s p.1,
      p125_fb_square_basis_mem_own_grade K q s p.1⟩ ⊗ₜ[K]
    ⟨cwSquareCanonicalBasis K q s p.2,
      p125_fb_square_basis_mem_own_grade K q s p.2⟩
  have hz := TensorObj.TypeGrading.classKronEmbed_mem
    G G s (cwSquarePairGrade q p.1) (cwSquarePairGrade q p.2) z
  have heq :
      cwFourthCanonicalBasis K q s p =
        TensorObj.TypeGrading.classKronEmbed
          G G s (cwSquarePairGrade q p.1) (cwSquarePairGrade q p.2) z := by
    rw [p125_fb_fourth_basis_apply]
    rfl
  rw [heq]
  change
    TensorObj.TypeGrading.classKronEmbed
        G G s (cwSquarePairGrade q p.1) (cwSquarePairGrade q p.2) z ∈
      (TensorObj.TypeGrading.kronGrading G G).classOf s
        (finProdFinEquiv
          (cwSquarePairGrade q p.1, cwSquarePairGrade q p.2))
  exact hz

private theorem p125_fb_fine_pair_mem_coarse
    (q : ℕ) (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2)))
    (hp : cwSquarePairGrade q p.1 = sx s ∧
      cwSquarePairGrade q p.2 = sy s) :
    cwFourthPairGrade q p = modeTotalGrade s := by
  apply Fin.ext
  simpa only [cwFourthPairGrade, hp.1, hp.2] using hsum s

/-- Inside the fixed coarse type `(2,3,3)`, remembering the first square
grade is equivalent to remembering the complete ordered pair of fine grades. -/
private theorem p125_fb_outerGrade_eq_iff_fine_pair
    (q : ℕ) (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) (p : ModeIndex q s) :
    outerGrade q s p = sx s ↔
      cwSquarePairGrade q p.1.1 = sx s ∧
        cwSquarePairGrade q p.1.2 = sy s := by
  have hcoarse := congrArg Fin.val p.2
  constructor
  · intro hfirst
    have hx : cwSquarePairGrade q p.1.1 = sx s := by
      simpa only [outerGrade] using hfirst
    refine ⟨hx, ?_⟩
    apply Fin.ext
    have hxv := congrArg Fin.val hx
    have htotal := hsum s
    simp only [cwFourthPairGrade] at hcoarse
    omega
  · rintro ⟨hx, _⟩
    simpa only [outerGrade] using hx

private theorem p125_fb_outer_blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin 5)
    (p : ModeIndex q s) :
    (outerGrading K q).blockProj s a (canonicalBasis K q s p) =
      if h : outerGrade q s p = a then
        ⟨canonicalBasis K q s p, by
          change canonicalBasis K q s p ∈
            cwBasisGrade (canonicalBasis K q s) (outerGrade q s) a
          simpa only [h] using p125_fb_canonical_basis_mem_grade
            (canonicalBasis K q s) (outerGrade q s) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (outerGrading K q) s (outerGrade q s p) _
      (p125_fb_canonical_basis_mem_grade
        (canonicalBasis K q s) (outerGrade q s) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (outerGrading K q) s a (outerGrade q s p) (Ne.symm h) _
      (p125_fb_canonical_basis_mem_grade
        (canonicalBasis K q s) (outerGrade q s) p)

private theorem p125_fb_outer_class_le_fine_comap
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) :
    (outerGrading K q).classOf s (sx s) ≤
      Submodule.comap
        ((cwFourthCanonicalGrading K q).classOf s
          (modeTotalGrade s)).subtype
        ((TensorObj.TypeGrading.kronGrading
          (cwSquareCanonicalGrading K q)
          (cwSquareCanonicalGrading K q)).classOf s
            (finProdFinEquiv (sx s, sy s))) := by
  change cwBasisGrade (canonicalBasis K q s)
      (outerGrade q s) (sx s) ≤ _
  unfold cwBasisGrade
  apply Submodule.span_le.2
  rintro _ ⟨p, hp, rfl⟩
  change (canonicalBasis K q s p).val ∈
    (TensorObj.TypeGrading.kronGrading
      (cwSquareCanonicalGrading K q)
      (cwSquareCanonicalGrading K q)).classOf s
        (finProdFinEquiv (sx s, sy s))
  rw [canonicalBasis_coe]
  have hm := p125_fb_fourth_basis_mem_own_fine_grade K q s p.1
  obtain ⟨hx, hy⟩ := (p125_fb_outerGrade_eq_iff_fine_pair q sx sy hsum s p).mp hp
  simpa only [hx, hy] using hm

/-- Canonical inclusion of one outer mode block into its literal fine block. -/
private noncomputable def p125_fb_outerClassToFine
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) :
    (outerGrading K q).classOf s (sx s) →ₗ[K]
      (TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).classOf s
          (finProdFinEquiv (sx s, sy s)) :=
  LinearMap.codRestrict _
    (((cwFourthCanonicalGrading K q).classOf s
      (modeTotalGrade s)).subtype.comp
        ((outerGrading K q).classOf s (sx s)).subtype)
    (fun x => p125_fb_outer_class_le_fine_comap K q sx sy hsum s x.property)

@[simp] private theorem outerClassToFine_coe
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) (x : (outerGrading K q).classOf s (sx s)) :
    (p125_fb_outerClassToFine K q sx sy hsum s x).val = x.1.1 := by
  rfl

private theorem p125_fb_coarse_blockProj_fourth_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    (cwFourthCanonicalGrading K q).blockProj s
        (modeTotalGrade s) (cwFourthCanonicalBasis K q s p) =
      if h : cwFourthPairGrade q p = modeTotalGrade s then
        canonicalBasis K q s ⟨p, h⟩
      else 0 := by
  split_ifs with h
  · rw [TensorObj.TypeGrading.blockProj_apply_mem]
    · apply Subtype.ext
      exact (canonicalBasis_coe K q s ⟨p, h⟩).symm
    · change cwFourthCanonicalBasis K q s p ∈
        cwBasisGrade (cwFourthCanonicalBasis K q s)
          (cwFourthPairGrade q) (modeTotalGrade s)
      simpa only [h] using p125_fb_canonical_basis_mem_grade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K q) s (modeTotalGrade s)
      (cwFourthPairGrade q p) (Ne.symm h) _
      (p125_fb_canonical_basis_mem_grade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)

private theorem p125_fb_fine_blockProj_fourth_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (sx sy : Fin 3 → Fin 5)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    (TensorObj.TypeGrading.kronGrading
      (cwSquareCanonicalGrading K q)
      (cwSquareCanonicalGrading K q)).blockProj s
        (finProdFinEquiv (sx s, sy s))
        (cwFourthCanonicalBasis K q s p) =
      if h : cwSquarePairGrade q p.1 = sx s ∧
          cwSquarePairGrade q p.2 = sy s then
        ⟨cwFourthCanonicalBasis K q s p, by
          obtain ⟨hx, hy⟩ := h
          change cwFourthCanonicalBasis K q s p ∈
            (TensorObj.TypeGrading.kronGrading
              (cwSquareCanonicalGrading K q)
              (cwSquareCanonicalGrading K q)).classOf s
                (finProdFinEquiv (sx s, sy s))
          simpa only [hx, hy] using
            p125_fb_fourth_basis_mem_own_fine_grade K q s p⟩
      else 0 := by
  let G := TensorObj.TypeGrading.kronGrading
    (cwSquareCanonicalGrading K q) (cwSquareCanonicalGrading K q)
  let own := finProdFinEquiv
    (cwSquarePairGrade q p.1, cwSquarePairGrade q p.2)
  have hp : cwFourthCanonicalBasis K q s p ∈ G.classOf s own :=
    p125_fb_fourth_basis_mem_own_fine_grade K q s p
  split_ifs with h
  · obtain ⟨hx, hy⟩ := h
    exact TensorObj.TypeGrading.blockProj_apply_mem G s
      (finProdFinEquiv (sx s, sy s)) _ (by
        have hown : own = finProdFinEquiv (sx s, sy s) := by
          simp only [own, hx, hy]
        change cwFourthCanonicalBasis K q s p ∈
          G.classOf s (finProdFinEquiv (sx s, sy s))
        rw [← hown]
        exact hp)
  · have hne : finProdFinEquiv (sx s, sy s) ≠ own := by
      intro heq
      have hpair := finProdFinEquiv.injective heq
      apply h
      exact ⟨(congrArg Prod.fst hpair).symm,
        (congrArg Prod.snd hpair).symm⟩
    exact TensorObj.TypeGrading.blockProj_apply_mem_ne G s
      (finProdFinEquiv (sx s, sy s)) own hne _ hp

private theorem p125_fb_outerFine_projection_comp
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) :
    (p125_fb_outerClassToFine K q sx sy hsum s).comp
        (((outerGrading K q).blockProj s (sx s)).comp
          ((cwFourthCanonicalGrading K q).blockProj s
            (modeTotalGrade s))) =
      (TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockProj s
          (finProdFinEquiv (sx s, sy s)) := by
  apply (cwFourthCanonicalBasis K q s).ext
  intro p
  simp only [LinearMap.comp_apply]
  by_cases hc : cwFourthPairGrade q p = modeTotalGrade s
  · have hcproj := p125_fb_coarse_blockProj_fourth_basis K q s p
    rw [dif_pos hc] at hcproj
    let pc : ModeIndex q s := ⟨p, hc⟩
    have hcstep := congrArg (fun x =>
      p125_fb_outerClassToFine K q sx sy hsum s
        ((outerGrading K q).blockProj s (sx s) x)) hcproj
    by_cases ho : outerGrade q s pc = sx s
    · have hoproj := p125_fb_outer_blockProj_basis K q s (sx s) pc
      rw [dif_pos ho] at hoproj
      have hfine := (p125_fb_outerGrade_eq_iff_fine_pair q sx sy hsum s pc).mp ho
      change cwSquarePairGrade q p.1 = sx s ∧
        cwSquarePairGrade q p.2 = sy s at hfine
      have hfproj := p125_fb_fine_blockProj_fourth_basis K q s sx sy p
      rw [dif_pos hfine] at hfproj
      calc
        _ = p125_fb_outerClassToFine K q sx sy hsum s
              ((outerGrading K q).blockProj s (sx s)
                (canonicalBasis K q s pc)) := hcstep
        _ = p125_fb_outerClassToFine K q sx sy hsum s
              ⟨canonicalBasis K q s pc, by
                change canonicalBasis K q s pc ∈
                  cwBasisGrade (canonicalBasis K q s)
                    (outerGrade q s) (sx s)
                simpa only [ho] using p125_fb_canonical_basis_mem_grade
                  (canonicalBasis K q s) (outerGrade q s) pc⟩ :=
            congrArg (p125_fb_outerClassToFine K q sx sy hsum s) hoproj
        _ = ⟨cwFourthCanonicalBasis K q s p, by
              change cwFourthCanonicalBasis K q s p ∈
                (TensorObj.TypeGrading.kronGrading
                  (cwSquareCanonicalGrading K q)
                  (cwSquareCanonicalGrading K q)).classOf s
                    (finProdFinEquiv (sx s, sy s))
              simpa only [hfine.1, hfine.2] using
                p125_fb_fourth_basis_mem_own_fine_grade K q s p⟩ := by
            apply Subtype.ext
            exact canonicalBasis_coe K q s pc
        _ = _ := hfproj.symm
    · have hoproj := p125_fb_outer_blockProj_basis K q s (sx s) pc
      rw [dif_neg ho] at hoproj
      have hfine : ¬(cwSquarePairGrade q p.1 = sx s ∧
          cwSquarePairGrade q p.2 = sy s) := by
        intro hp
        exact ho ((p125_fb_outerGrade_eq_iff_fine_pair q sx sy hsum s pc).mpr hp)
      have hfproj := p125_fb_fine_blockProj_fourth_basis K q s sx sy p
      rw [dif_neg hfine] at hfproj
      calc
        _ = p125_fb_outerClassToFine K q sx sy hsum s
              ((outerGrading K q).blockProj s (sx s)
                (canonicalBasis K q s pc)) := hcstep
        _ = p125_fb_outerClassToFine K q sx sy hsum s 0 :=
          congrArg (p125_fb_outerClassToFine K q sx sy hsum s) hoproj
        _ = 0 := map_zero _
        _ = _ := hfproj.symm
  · have hcproj := p125_fb_coarse_blockProj_fourth_basis K q s p
    rw [dif_neg hc] at hcproj
    have hfine : ¬(cwSquarePairGrade q p.1 = sx s ∧
        cwSquarePairGrade q p.2 = sy s) := by
      intro hp
      exact hc (p125_fb_fine_pair_mem_coarse q sx sy hsum s p hp)
    have hfproj := p125_fb_fine_blockProj_fourth_basis K q s sx sy p
    rw [dif_neg hfine] at hfproj
    calc
      _ = p125_fb_outerClassToFine K q sx sy hsum s
            ((outerGrading K q).blockProj s (sx s) 0) :=
          congrArg (fun x =>
            p125_fb_outerClassToFine K q sx sy hsum s
              ((outerGrading K q).blockProj s (sx s) x)) hcproj
      _ = 0 := by simp only [map_zero]
      _ = _ := hfproj.symm

private theorem p125_fb_piTensorMap_three
    {K : Type u} [Field K]
    {d : ℕ} {V₀ V₁ V₂ V₃ : Fin d → Type u}
    [∀ i, AddCommGroup (V₀ i)] [∀ i, Module K (V₀ i)]
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    (f : ∀ i, V₂ i →ₗ[K] V₃ i)
    (g : ∀ i, V₁ i →ₗ[K] V₂ i)
    (h : ∀ i, V₀ i →ₗ[K] V₁ i)
    (x : PiTensorProduct K V₀) :
    PiTensorProduct.map f
        (PiTensorProduct.map g (PiTensorProduct.map h x)) =
      PiTensorProduct.map
        (fun i => ((f i).comp (g i)).comp (h i)) x := by
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]

/-- A literal fine block of `phi_233` is a restriction of the matching block
of the internal five-grading of the actual coarse constituent. -/
theorem fineBlock_restrict_outerBlock
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val) :
    TensorObj.Restrict
      ((TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockSubtensor
          (fun s => finProdFinEquiv (sx s, sy s)))
      ((outerGrading K q).blockSubtensor sx) := by
  refine ⟨fun s => p125_fb_outerClassToFine K q sx sy hsum s, ?_⟩
  change PiTensorProduct.map
      (fun s => p125_fb_outerClassToFine K q sx sy hsum s)
      (PiTensorProduct.map
        (fun s => (outerGrading K q).blockProj s (sx s))
        (PiTensorProduct.map
          (fun s => (cwFourthCanonicalGrading K q).blockProj s
            (modeTotalGrade s))
          (cwFourthObj K q).t)) =
    PiTensorProduct.map
      (fun s =>
        (TensorObj.TypeGrading.kronGrading
          (cwSquareCanonicalGrading K q)
          (cwSquareCanonicalGrading K q)).blockProj s
            (finProdFinEquiv (sx s, sy s)))
      (cwFourthObj K q).t
  calc
    _ = PiTensorProduct.map (fun s =>
          ((p125_fb_outerClassToFine K q sx sy hsum s).comp
            ((outerGrading K q).blockProj s (sx s))).comp
              ((cwFourthCanonicalGrading K q).blockProj s
                (modeTotalGrade s))) (cwFourthObj K q).t :=
      p125_fb_piTensorMap_three
        (fun s => p125_fb_outerClassToFine K q sx sy hsum s)
        (fun s => (outerGrading K q).blockProj s (sx s))
        (fun s => (cwFourthCanonicalGrading K q).blockProj s
          (modeTotalGrade s)) (cwFourthObj K q).t
    _ = _ := by
      congr 1
      congr 1
      funext s
      apply LinearMap.ext
      intro x
      exact DFunLike.congr_fun
        (p125_fb_outerFine_projection_comp K q sx sy hsum s) x

end MME.StothersFourth.Phi125

open MME.StothersFourth.Phi125

set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

theorem phi125_fine_block_restrict_outer_block
    {K : Type u} [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val) :
    TensorObj.Restrict
      ((TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockSubtensor
          (fun s => finProdFinEquiv (sx s, sy s)))
      ((outerGrading K q).blockSubtensor sx) :=
  fineBlock_restrict_outerBlock K q sx sy hsum
end

section
open MME TensorProduct PiTensorProduct BigOperators Module


set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

namespace MME.StothersFourth.Phi125

private theorem p125_support_basis_mem_cwBasisGrade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι κ : Type*} [DecidableEq κ]
    (b : Basis ι K V) (g : ι -> κ) (i : ι) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private def p125_support_cwVec
    (K : Type u) [Field K] (q : Nat) (s : Fin 3) (a : Fin (q + 2)) :
    CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => (Pi.single a 1 : Fin (q + 2) -> K)
  | ⟨1, _⟩ => (Pi.single a 1 : Fin (q + 2) -> K)
  | ⟨2, _⟩ => (Pi.single a 1 : Fin (q + 2) -> K)

private theorem p125_support_literalTermMonomial_eq_tprod
    (K : Type u) [Field K] (q : Nat)
    (t : CWLiteralTerm q) :
    cwLiteralTermMonomial K q t =
      PiTensorProduct.tprod K
        (fun s => p125_support_cwVec K q s (cwLiteralTermTriple q t s)) := by
  unfold cwLiteralTermMonomial CWMonom
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem p125_support_squareCanonicalBasis_apply
    (K : Type u) [Field K] (q : Nat) (s : Fin 3)
    (a b : Fin (q + 2)) :
    cwSquareCanonicalBasis K q s (a, b) =
      p125_support_cwVec K q s a ⊗ₜ[K] p125_support_cwVec K q s b := by
  letI : IsScalarTower K K (Fin (q + 2) -> K) :=
    IsScalarTower.of_algebraMap_smul (by simp)
  fin_cases s <;>
    change (Module.Basis.tensorProduct (R := K) (S := K)
      (Pi.basisFun K (Fin (q + 2)))
      (Pi.basisFun K (Fin (q + 2)))) (a, b) = _ <;>
    rw [Module.Basis.tensorProduct_apply] <;>
    simp [p125_support_cwVec, Pi.basisFun_apply]

private theorem p125_support_fourthCanonicalBasis_apply
    (K : Type u) [Field K] (q : Nat) (s : Fin 3)
    (p :
      (Fin (q + 2) × Fin (q + 2)) ×
        (Fin (q + 2) × Fin (q + 2))) :
    cwFourthCanonicalBasis K q s p =
      cwSquareCanonicalBasis K q s p.1 ⊗ₜ[K]
        cwSquareCanonicalBasis K q s p.2 := by
  unfold cwFourthCanonicalBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

private theorem p125_support_interchange_tprod
    {K : Type u} [Field K] {d : Nat}
    {V W : Fin d -> Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (PiTensorProduct.tprod K v)
        (PiTensorProduct.tprod K w) =
      PiTensorProduct.tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (PiTensorProduct.tprod K v))
      (PiTensorProduct.tprod K w) = _
  rw [interchange]
  change (PiTensorProduct.lift interchangeOuter
      (PiTensorProduct.tprod K v)) (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v))
      (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem p125_support_fourLiteralTerms_eq_basis_tprod
    (K : Type u) [Field K] (q : Nat)
    (t₁ t₂ t₃ t₄ : CWLiteralTerm q) :
    interchange
        (interchange (cwLiteralTermMonomial K q t₁)
          (cwLiteralTermMonomial K q t₂))
        (interchange (cwLiteralTermMonomial K q t₃)
          (cwLiteralTermMonomial K q t₄)) =
      PiTensorProduct.tprod K (fun s =>
        cwFourthCanonicalBasis K q s
          (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s)) := by
  rw [p125_support_literalTermMonomial_eq_tprod, p125_support_literalTermMonomial_eq_tprod,
    p125_support_literalTermMonomial_eq_tprod, p125_support_literalTermMonomial_eq_tprod,
    p125_support_interchange_tprod, p125_support_interchange_tprod, p125_support_interchange_tprod]
  congr 1
  funext s
  rw [p125_support_fourthCanonicalBasis_apply,
    p125_support_squareCanonicalBasis_apply, p125_support_squareCanonicalBasis_apply]
  rfl

private theorem p125_support_coarse_blockProj_fourth_basis
    (K : Type u) [Field K] (q : Nat) (s : Fin 3)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    (cwFourthCanonicalGrading K q).blockProj s
        (modeTotalGrade s) (cwFourthCanonicalBasis K q s p) =
      if h : cwFourthPairGrade q p = modeTotalGrade s then
        canonicalBasis K q s ⟨p, h⟩
      else 0 := by
  split_ifs with h
  · rw [TensorObj.TypeGrading.blockProj_apply_mem]
    · apply Subtype.ext
      exact (canonicalBasis_coe K q s ⟨p, h⟩).symm
    · change cwFourthCanonicalBasis K q s p ∈
        cwBasisGrade (cwFourthCanonicalBasis K q s)
          (cwFourthPairGrade q) (modeTotalGrade s)
      simpa only [h] using p125_support_basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K q) s (modeTotalGrade s)
      (cwFourthPairGrade q p) (Ne.symm h) _
      (p125_support_basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)

private theorem p125_support_outer_blockProj_basis
    (K : Type u) [Field K] (q : Nat) (s : Fin 3) (a : Fin 5)
    (p : ModeIndex q s) :
    (outerGrading K q).blockProj s a (canonicalBasis K q s p) =
      if h : outerGrade q s p = a then
        ⟨canonicalBasis K q s p, by
          change canonicalBasis K q s p ∈
            cwBasisGrade (canonicalBasis K q s) (outerGrade q s) a
          simpa only [h] using p125_support_basis_mem_cwBasisGrade
            (canonicalBasis K q s) (outerGrade q s) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (outerGrading K q) s (outerGrade q s p) _
      (p125_support_basis_mem_cwBasisGrade
        (canonicalBasis K q s) (outerGrade q s) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (outerGrading K q) s a (outerGrade q s p) (Ne.symm h) _
      (p125_support_basis_mem_cwBasisGrade
        (canonicalBasis K q s) (outerGrade q s) p)

private theorem p125_support_coordGrade_zero (q : Nat) :
    cwSquareCoordGrade q (cwZeroIndex q) = 0 := by
  simp [cwSquareCoordGrade, cwZeroIndex]

private theorem p125_support_coordGrade_middle (q : Nat) (i : Fin q) :
    cwSquareCoordGrade q (cwMiddleIndex q i) = 1 := by
  simp [cwSquareCoordGrade, cwMiddleIndex]
  omega

private theorem p125_support_coordGrade_top (q : Nat) :
    cwSquareCoordGrade q (cwTopIndex q) = 2 := by
  simp [cwSquareCoordGrade, cwTopIndex]

private theorem p125_support_literalTerm_grade_sum_two
    (q : Nat) (t : CWLiteralTerm q) :
    (cwSquareCoordGrade q (cwLiteralTermTriple q t 0)).val +
      (cwSquareCoordGrade q (cwLiteralTermTriple q t 1)).val +
      (cwSquareCoordGrade q (cwLiteralTermTriple q t 2)).val = 2 := by
  rcases t with ⟨i, r⟩ | r <;> fin_cases r <;>
    simp [cwLiteralTermTriple, p125_support_coordGrade_zero,
      p125_support_coordGrade_middle, p125_support_coordGrade_top]

private def p125_support_firstSquareType (q : Nat)
    (t₁ t₂ : CWLiteralTerm q) (s : Fin 3) : Fin 5 :=
  cwSquarePairGrade q
    (cwLiteralTermTriple q t₁ s, cwLiteralTermTriple q t₂ s)

private def p125_support_secondSquareType (q : Nat)
    (t₃ t₄ : CWLiteralTerm q) (s : Fin 3) : Fin 5 :=
  cwSquarePairGrade q
    (cwLiteralTermTriple q t₃ s, cwLiteralTermTriple q t₄ s)

private theorem p125_support_firstSquareType_grade_sum_four
    (q : Nat) (t₁ t₂ : CWLiteralTerm q) :
    (p125_support_firstSquareType q t₁ t₂ 0).val +
      (p125_support_firstSquareType q t₁ t₂ 1).val +
      (p125_support_firstSquareType q t₁ t₂ 2).val = 4 := by
  have h₁ := p125_support_literalTerm_grade_sum_two q t₁
  have h₂ := p125_support_literalTerm_grade_sum_two q t₂
  simp only [p125_support_firstSquareType, cwSquarePairGrade]
  omega

private theorem p125_support_secondSquareType_grade_sum_four
    (q : Nat) (t₃ t₄ : CWLiteralTerm q) :
    (p125_support_secondSquareType q t₃ t₄ 0).val +
      (p125_support_secondSquareType q t₃ t₄ 1).val +
      (p125_support_secondSquareType q t₃ t₄ 2).val = 4 := by
  have h₃ := p125_support_literalTerm_grade_sum_two q t₃
  have h₄ := p125_support_literalTerm_grade_sum_two q t₄
  simp only [p125_support_secondSquareType, cwSquarePairGrade]
  omega

private theorem p125_support_fourLiteralTerms_outer_pattern
    (q : Nat) (t₁ t₂ t₃ t₄ : CWLiteralTerm q)
    (hcoarse : ∀ s,
      cwFourthPairGrade q (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s) =
        modeTotalGrade s) :
    ∃ r : Fin 6,
      (fun s => p125_support_firstSquareType q t₁ t₂ s) = pattern r := by
  have hfirst := p125_support_firstSquareType_grade_sum_four q t₁ t₂
  have hsecond := p125_support_secondSquareType_grade_sum_four q t₃ t₄
  have hiVal := congrArg Fin.val (hcoarse 0)
  have hjVal := congrArg Fin.val (hcoarse 1)
  have hkVal := congrArg Fin.val (hcoarse 2)
  have hi : (p125_support_firstSquareType q t₁ t₂ 0).val +
      (p125_support_secondSquareType q t₃ t₄ 0).val = 1 := by
    simpa [p125_support_firstSquareType, p125_support_secondSquareType, cwFourthPairGrade,
      cwFourthIndexOfLiteralTerms, modeTotalGrade, cwFourthBlockType] using hiVal
  have hj : (p125_support_firstSquareType q t₁ t₂ 1).val +
      (p125_support_secondSquareType q t₃ t₄ 1).val = 2 := by
    simpa [p125_support_firstSquareType, p125_support_secondSquareType, cwFourthPairGrade,
      cwFourthIndexOfLiteralTerms, modeTotalGrade, cwFourthBlockType] using hjVal
  have hk : (p125_support_firstSquareType q t₁ t₂ 2).val +
      (p125_support_secondSquareType q t₃ t₄ 2).val = 5 := by
    simpa [p125_support_firstSquareType, p125_support_secondSquareType, cwFourthPairGrade,
      cwFourthIndexOfLiteralTerms, modeTotalGrade, cwFourthBlockType] using hkVal
  rcases mme_stothers_phi125_square_support_pair_classification
      (p125_support_firstSquareType q t₁ t₂ 0)
      (p125_support_firstSquareType q t₁ t₂ 1)
      (p125_support_firstSquareType q t₁ t₂ 2)
      (p125_support_secondSquareType q t₃ t₄ 0)
      (p125_support_secondSquareType q t₃ t₄ 1)
      (p125_support_secondSquareType q t₃ t₄ 2)
      hfirst hsecond hi hj hk with
    h | h | h | h | h | h
  all_goals rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  · refine ⟨0, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨1, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨2, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨3, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨4, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨5, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]

private theorem p125_support_projected_literal_zero_of_no_pattern
    (K : Type u) [Field K] (q : Nat)
    (sigma : Fin 3 -> Fin 5)
    (hunsupported : ∀ r : Fin 6, sigma ≠ pattern r)
    (t₁ t₂ t₃ t₄ : CWLiteralTerm q) :
    PiTensorProduct.map
        (fun s => (outerGrading K q).blockProj s (sigma s))
        (PiTensorProduct.map
          (fun s => (cwFourthCanonicalGrading K q).blockProj s
            (modeTotalGrade s))
          (interchange
            (interchange (cwLiteralTermMonomial K q t₁)
              (cwLiteralTermMonomial K q t₂))
            (interchange (cwLiteralTermMonomial K q t₃)
              (cwLiteralTermMonomial K q t₄)))) = 0 := by
  let F := fun x =>
    PiTensorProduct.map
      (fun s => (outerGrading K q).blockProj s (sigma s))
      (PiTensorProduct.map
        (fun s => (cwFourthCanonicalGrading K q).blockProj s
          (modeTotalGrade s)) x)
  calc
    _ = F (PiTensorProduct.tprod K (fun s =>
          cwFourthCanonicalBasis K q s
            (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s))) := by
      exact congrArg F (p125_support_fourLiteralTerms_eq_basis_tprod K q t₁ t₂ t₃ t₄)
    _ = 0 := by
      dsimp only [F]
      rw [PiTensorProduct.map_tprod]
      erw [PiTensorProduct.map_tprod]
      by_cases hcoarse : ∀ s,
          cwFourthPairGrade q
              (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s) =
            modeTotalGrade s
      · obtain ⟨r, hr⟩ := p125_support_fourLiteralTerms_outer_pattern
          q t₁ t₂ t₃ t₄ hcoarse
        have haddress :
            (fun s => p125_support_firstSquareType q t₁ t₂ s) ≠ sigma := by
          intro heq
          exact hunsupported r (heq.symm.trans hr)
        have hdiff : ∃ s,
            p125_support_firstSquareType q t₁ t₂ s ≠ sigma s := by
          by_contra hnone
          push Not at hnone
          exact haddress (funext hnone)
        obtain ⟨s, hs⟩ := hdiff
        apply (PiTensorProduct.tprod K).map_coord_zero s
        rw [p125_support_coarse_blockProj_fourth_basis, dif_pos (hcoarse s)]
        let pc : ModeIndex q s :=
          ⟨cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s, hcoarse s⟩
        change (outerGrading K q).blockProj s (sigma s)
          (canonicalBasis K q s pc) = 0
        rw [p125_support_outer_blockProj_basis, dif_neg]
        simpa [pc, outerGrade, p125_support_firstSquareType,
          cwFourthIndexOfLiteralTerms] using hs
      · push Not at hcoarse
        obtain ⟨s, hs⟩ := hcoarse
        apply (PiTensorProduct.tprod K).map_coord_zero s
        rw [p125_support_coarse_blockProj_fourth_basis, dif_neg hs]
        simp

private theorem p125_support_linearMap_pair_fintype_sum
    {R I M N P : Type*} [Semiring R] [Fintype I]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    (A : N →ₗ[R] P) (B : M →ₗ[R] N) (f : I → M) :
    A (B (∑ i, f i)) = ∑ i, A (B (f i)) := by
  rw [map_sum B, map_sum A]

private theorem p125_support_outer_block_zero_of_no_pattern
    (K : Type u) [Field K] (q : Nat)
    (sigma : Fin 3 -> Fin 5)
    (hunsupported : ∀ r : Fin 6, sigma ≠ pattern r) :
    (outerGrading K q).blockTensor sigma = 0 := by
  unfold TensorObj.TypeGrading.blockTensor
  change PiTensorProduct.map
      (fun s => (outerGrading K q).blockProj s (sigma s))
      (PiTensorProduct.map
        (fun s => (cwFourthCanonicalGrading K q).blockProj s
          (modeTotalGrade s))
        (cwFourthObj K q).t) = 0
  rw [mme_CW_fourth_tensor_eq_sum_literal_terms]
  let A := PiTensorProduct.map
    (fun s => (outerGrading K q).blockProj s (sigma s))
  let B := PiTensorProduct.map
    (fun s => (cwFourthCanonicalGrading K q).blockProj s
      (modeTotalGrade s))
  let f₄ := fun t₄ : CWLiteralTerm q =>
    ∑ t₃ : CWLiteralTerm q, ∑ t₂ : CWLiteralTerm q,
      ∑ t₁ : CWLiteralTerm q,
        interchange
          (interchange (cwLiteralTermMonomial K q t₁)
            (cwLiteralTermMonomial K q t₂))
          (interchange (cwLiteralTermMonomial K q t₃)
            (cwLiteralTermMonomial K q t₄))
  calc
    _ = ∑ t₄ : CWLiteralTerm q, A (B (f₄ t₄)) := by
      exact p125_support_linearMap_pair_fintype_sum A B f₄
    _ = 0 := by
      apply Fintype.sum_eq_zero
      intro t₄
      let f₃ := fun t₃ : CWLiteralTerm q =>
        ∑ t₂ : CWLiteralTerm q, ∑ t₁ : CWLiteralTerm q,
          interchange
            (interchange (cwLiteralTermMonomial K q t₁)
              (cwLiteralTermMonomial K q t₂))
            (interchange (cwLiteralTermMonomial K q t₃)
              (cwLiteralTermMonomial K q t₄))
      calc
        A (B (f₄ t₄)) =
            ∑ t₃ : CWLiteralTerm q, A (B (f₃ t₃)) := by
          dsimp only [f₄]
          exact p125_support_linearMap_pair_fintype_sum A B f₃
        _ = 0 := by
          apply Fintype.sum_eq_zero
          intro t₃
          let f₂ := fun t₂ : CWLiteralTerm q =>
            ∑ t₁ : CWLiteralTerm q,
              interchange
                (interchange (cwLiteralTermMonomial K q t₁)
                  (cwLiteralTermMonomial K q t₂))
                (interchange (cwLiteralTermMonomial K q t₃)
                  (cwLiteralTermMonomial K q t₄))
          calc
            A (B (f₃ t₃)) =
                ∑ t₂ : CWLiteralTerm q, A (B (f₂ t₂)) := by
              dsimp only [f₃]
              exact p125_support_linearMap_pair_fintype_sum A B f₂
            _ = 0 := by
              apply Fintype.sum_eq_zero
              intro t₂
              let f₁ := fun t₁ : CWLiteralTerm q =>
                interchange
                  (interchange (cwLiteralTermMonomial K q t₁)
                    (cwLiteralTermMonomial K q t₂))
                  (interchange (cwLiteralTermMonomial K q t₃)
                    (cwLiteralTermMonomial K q t₄))
              calc
                A (B (f₂ t₂)) =
                    ∑ t₁ : CWLiteralTerm q, A (B (f₁ t₁)) := by
                  dsimp only [f₂]
                  exact p125_support_linearMap_pair_fintype_sum A B f₁
                _ = 0 := by
                  apply Fintype.sum_eq_zero
                  intro t₁
                  dsimp only [A, B, f₁]
                  exact p125_support_projected_literal_zero_of_no_pattern
                    K q sigma hunsupported t₁ t₂ t₃ t₄

end MME.StothersFourth.Phi125

theorem phi125_outer_grading_support
    {K : Type u} [Field K] (q : Nat) (sigma : Fin 3 -> Fin 5)
    (h : (MME.StothersFourth.Phi125.outerGrading K q).blockTensor sigma ≠ 0) :
    ∃ r : Fin 6, sigma = MME.StothersFourth.Phi125.pattern r := by
  by_contra hnone
  push Not at hnone
  exact h (MME.StothersFourth.Phi125.p125_support_outer_block_zero_of_no_pattern
    K q sigma hnone)
end

section
open MME BigOperators
open MME.StothersFourth.Phi125
set_option autoImplicit false
set_option maxHeartbeats 300000

namespace MME.StothersFourth.Phi125
noncomputable def fineSourceObj (K : Type u) [Field K] (q : ℕ) : Fin 6 → TensorObj K 3 :=
  ![Phi116.cwFourthFineBlockObj K q 0 0 4 1 2 1,
    Phi116.cwFourthFineBlockObj K q 0 1 3 1 1 2,
    Phi116.cwFourthFineBlockObj K q 0 2 2 1 0 3,
    Phi116.cwFourthFineBlockObj K q 1 0 3 0 2 2,
    Phi116.cwFourthFineBlockObj K q 1 1 2 0 1 3,
    Phi116.cwFourthFineBlockObj K q 1 2 1 0 0 4]
noncomputable def componentObj (K : Type u) [Field K] (q : ℕ) : Fin 6 → TensorObj K 3 :=
  ![TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q),
    TensorObj.kron (MMObj K 1 1 (2*q)) (coupledObj K q),
    MMObj K (2*q) 1 (q^2+2),
    MMObj K (2*q) 1 (q^2+2),
    TensorObj.kron (coupledObj K q) (MMObj K 1 1 (2*q)),
    TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)]
end MME.StothersFourth.Phi125

theorem phi125_kron_restrict
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  rw [← TensorQ.le_toQ]
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft : P.le
      (TensorQ.toQ X * TensorQ.toQ Y)
      (TensorQ.toQ X' * TensorQ.toQ Y) :=
    P.mul_right _ _ hx _
  have hright : P.le
      (TensorQ.toQ X' * TensorQ.toQ Y)
      (TensorQ.toQ X' * TensorQ.toQ Y') := by
    simpa only [mul_comm] using P.mul_right _ _ hy (TensorQ.toQ X')
  exact P.le_trans _ _ _ hleft hright

theorem phi125_kronFin_restrict
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d) :
    ∀ (n : ℕ) (X Y : Fin n → TensorObj K d),
      (∀ r, TensorObj.Restrict (X r) (Y r)) →
      TensorObj.Restrict (TensorObj.kronFin n X)
        (TensorObj.kronFin n Y) := by
  intro n
  induction n with
  | zero =>
      intro X Y _
      exact TensorObj.Restrict.refl _
  | succ n ih =>
      intro X Y h
      change TensorObj.Restrict
        (TensorObj.kron (X 0)
          (TensorObj.kronFin n (fun r ↦ X r.succ)))
        (TensorObj.kron (Y 0)
          (TensorObj.kronFin n (fun r ↦ Y r.succ)))
      exact phi125_kron_restrict hd (h 0)
        (ih (fun r ↦ X r.succ) (fun r ↦ Y r.succ)
          (fun r ↦ h r.succ))

theorem phi125_fine_source_restrict {K : Type u} [Field K] (q : ℕ) (r : Fin 6) :
    TensorObj.Restrict (fineSourceObj K q r) ((outerGrading K q).blockSubtensor (pattern r)) := by
  fin_cases r
  · have hp : pattern (0 : Fin 6)=cwSquareBlockType 0 0 4 := by funext s; fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict (fineSourceObj K q (0 : Fin 6))
      ((outerGrading K q).blockSubtensor f)) hp).mpr
    exact phi125_fine_block_restrict_outer_block (K := K) q (cwSquareBlockType 0 0 4) (cwSquareBlockType 1 2 1)
      (by intro s; fin_cases s <;> rfl)
  · have hp : pattern (1 : Fin 6)=cwSquareBlockType 0 1 3 := by funext s; fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict (fineSourceObj K q (1 : Fin 6))
      ((outerGrading K q).blockSubtensor f)) hp).mpr
    exact phi125_fine_block_restrict_outer_block (K := K) q (cwSquareBlockType 0 1 3) (cwSquareBlockType 1 1 2)
      (by intro s; fin_cases s <;> rfl)
  · have hp : pattern (2 : Fin 6)=cwSquareBlockType 0 2 2 := by funext s; fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict (fineSourceObj K q (2 : Fin 6))
      ((outerGrading K q).blockSubtensor f)) hp).mpr
    exact phi125_fine_block_restrict_outer_block (K := K) q (cwSquareBlockType 0 2 2) (cwSquareBlockType 1 0 3)
      (by intro s; fin_cases s <;> rfl)
  · have hp : pattern (3 : Fin 6)=cwSquareBlockType 1 0 3 := by funext s; fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict (fineSourceObj K q (3 : Fin 6))
      ((outerGrading K q).blockSubtensor f)) hp).mpr
    exact phi125_fine_block_restrict_outer_block (K := K) q (cwSquareBlockType 1 0 3) (cwSquareBlockType 0 2 2)
      (by intro s; fin_cases s <;> rfl)
  · have hp : pattern (4 : Fin 6)=cwSquareBlockType 1 1 2 := by funext s; fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict (fineSourceObj K q (4 : Fin 6))
      ((outerGrading K q).blockSubtensor f)) hp).mpr
    exact phi125_fine_block_restrict_outer_block (K := K) q (cwSquareBlockType 1 1 2) (cwSquareBlockType 0 1 3)
      (by intro s; fin_cases s <;> rfl)
  · have hp : pattern (5 : Fin 6)=cwSquareBlockType 1 2 1 := by funext s; fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict (fineSourceObj K q (5 : Fin 6))
      ((outerGrading K q).blockSubtensor f)) hp).mpr
    exact phi125_fine_block_restrict_outer_block (K := K) q (cwSquareBlockType 1 2 1) (cwSquareBlockType 0 0 4)
      (by intro s; fin_cases s <;> rfl)

theorem phi125_component_restrict {K : Type u} [Field K] (q : ℕ) (r : Fin 6) :
    TensorObj.Restrict (componentObj K q r) (fineSourceObj K q r) := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := mme_stothers_phi125_fine_component_restrictions (K := K) q
  fin_cases r
  · simpa [componentObj, fineSourceObj] using h0
  · simpa [componentObj, fineSourceObj] using h1
  · simpa [componentObj, fineSourceObj] using h2
  · simpa [componentObj, fineSourceObj] using h3
  · simpa [componentObj, fineSourceObj] using h4
  · simpa [componentObj, fineSourceObj] using h5

theorem phi125_exact_product_restrict {K : Type u} [Field K] (q : ℕ) {N a b c : ℕ}
    (w : ExactProfileWord N a b c) :
    TensorObj.Restrict
      (TensorObj.kronFin 6 (fun r ↦ (componentObj K q r).kronPow (profileMultiplicity a b c r)))
      (gradedAddressBlock (outerGrading K q) (modeWord w.1)) := by
  classical
  have hgroup := mme_kronFin_group_by_exact_fibers_iso (componentObj K q) w.1
    (profileMultiplicity a b c) (by intro r; rw [Fintype.card_subtype]; exact w.2 r)
  refine hgroup.2.trans (phi125_kronFin_restrict (d := 3) (by omega) (2*N) _ _ ?_)
  intro j
  exact (phi125_component_restrict (K := K) q (w.1 j)).trans (phi125_fine_source_restrict (K := K) q (w.1 j))

def phi125_cyclic_address {N a b c : ℕ} (e : CyclicExactEdge N a b c) : Fin 3 → Fin (2*N) → Fin 125 :=
  fun i j ↦ mmeCyclicTripleGrade (fun s ↦ modeWord e.1.1 s j)
    (fun s ↦ modeWord e.2.1.1 s j) (fun s ↦ modeWord e.2.2.1 s j) i

theorem phi125_cyclic_product_restrict {K : Type u} [Field K] (q : ℕ) {N a b c : ℕ}
    (e : CyclicExactEdge N a b c) :
    TensorObj.Restrict
      (cyclicSymmetrization (TensorObj.kronFin 6
        (fun r ↦ (componentObj K q r).kronPow (profileMultiplicity a b c r))))
      (gradedAddressBlock (mmeCyclicTripleGrading (outerGrading K q)) (phi125_cyclic_address e)) := by
  have hA := phi125_exact_product_restrict (K := K) q e.1
  have hB := phi125_exact_product_restrict (K := K) q e.2.1
  have hC := phi125_exact_product_restrict (K := K) q e.2.2
  have hh := phi125_kron_restrict (K := K) (by omega) hA
    (phi125_kron_restrict (K := K) (by omega)
      (TensorObj.permObj_restrict cyclicPerm hB)
      (TensorObj.permObj_restrict (cyclicPerm.trans cyclicPerm) hC))
  rw [cyclicSymmetrization_eq_public_perm]
  exact hh.trans (mme_cyclic_grading_address_block_iso (outerGrading K q)
    (modeWord e.1.1) (modeWord e.2.1.1) (modeWord e.2.2.1)).1
end

section
open BigOperators
open MME.StothersFourth.Phi125

set_option autoImplicit false
set_option warningAsError true

theorem phi125_hash_difference
    {p N alpha beta gamma : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e f : CyclicExactEdge N alpha beta gamma) :
    cyclicAffineHash p N alpha beta gamma w shift offset i e -
        cyclicAffineHash p N alpha beta gamma w shift offset i f =
      ∑ r : Fin 3, ∑ j : Fin (2 * N),
        (cyclicHashModeCode p N i (cyclicModeWord e i) r j -
          cyclicHashModeCode p N i (cyclicModeWord f i) r j) * w r j := by
  rw [mme_stothers_phi125_cyclic_affine_hash_normal_form w shift offset i e,
    mme_stothers_phi125_cyclic_affine_hash_normal_form w shift offset i f]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  ring

open BigOperators
open MME.StothersFourth.Phi125

set_option autoImplicit false
set_option warningAsError true

theorem phi125_hash_edge
    {p N alpha beta gamma : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e : CyclicExactEdge N alpha beta gamma)
    (S : Finset (ZMod p)) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : (I → ZMod p) × ZMod p) (i : Fin 3) ↦
      cyclicAffineHash p N alpha beta gamma
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i e
    ((Finset.univ.filter
      (fun q ↦ ∃ s ∈ S, ∀ i : Fin 3, H q i = s)).card) =
      S.card * p ^ (6 * N) := by
  classical
  dsimp only
  let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
  let weights := fun w : I → ZMod p ↦
    fun r j ↦ w (Sum.inl (r, j))
  let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
  let H := fun (q : (I → ZMod p) × ZMod p) (i : Fin 3) ↦
    cyclicAffineHash p N alpha beta gamma
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i e
  change ((Finset.univ.filter
    (fun q : (I → ZMod p) × ZMod p ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i = s)).card) = _
  have hcard : Fintype.card I = 6 * N + 1 := by
    simp [I]
    omega
  let c : I → ZMod p
    | Sum.inl x => cyclicHashModeCode p N 0
        (cyclicModeWord e 0) x.1 x.2
    | Sum.inr _ => 1
  have hc : c (Sum.inr ()) ≠ 0 := by
    simp [c]
  let L0 : (I → ZMod p) → ZMod p := fun w ↦
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cyclicHashModeCode p N 0 (cyclicModeWord e 0) r j *
        w (Sum.inl (r, j))
  let L2 : (I → ZMod p) → ZMod p := fun w ↦
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cyclicHashModeCode p N 2 (cyclicModeWord e 2) r j *
        w (Sum.inl (r, j))
  let offset : (I → ZMod p) → ZMod p := fun w ↦ L0 w - L2 w
  have h6 : (6 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 6 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hH0 (q : (I → ZMod p) × ZMod p) :
      H q 0 = shift q.1 + L0 q.1 := by
    simpa [H, weights, shift, L0] using
      (mme_stothers_phi125_cyclic_affine_hash_normal_form
        (p := p) (N := N) (alpha := alpha) (beta := beta)
        (gamma := gamma) 
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) 0 e)
  have hH2 (q : (I → ZMod p) × ZMod p) :
      H q 2 = shift q.1 + q.2 + L2 q.1 := by
    rw [show H q 2 =
        shift q.1 + 6 * ((6 : ZMod p)⁻¹ * q.2) + L2 q.1 by
      simpa [H, weights, shift, L2] using
        (mme_stothers_phi125_cyclic_affine_hash_normal_form
          (p := p) (N := N) (alpha := alpha) (beta := beta)
          (gamma := gamma) 
          (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) 2 e)]
    rw [← mul_assoc, mul_inv_cancel₀ h6, one_mul]
  have hAP (q : (I → ZMod p) × ZMod p) :
      H q 0 + H q 1 = 2 * H q 2 := by
    have hsupp : CyclicCoordinatewiseSupported e e e := by
      refine ⟨?_, ?_, ?_⟩
      · intro j; exact ⟨e.1.1 j,rfl,rfl,rfl⟩
      · intro j; exact ⟨e.2.1.1 j,rfl,rfl,rfl⟩
      · intro j; exact ⟨e.2.2.1 j,rfl,rfl,rfl⟩
    exact mme_stothers_phi125_cyclic_affine_hash_AP
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2)
      e e e hsupp
  have hret (q : (I → ZMod p) × ZMod p) :
      (∃ s ∈ S, ∀ i : Fin 3, H q i = s) ↔
        shift q.1 + L0 q.1 ∈ S ∧ q.2 = offset q.1 := by
    constructor
    · rintro ⟨s, hs, hcommon⟩
      refine ⟨?_, ?_⟩
      · have h0 := hcommon 0
        rw [hH0 q] at h0
        exact h0 ▸ hs
      · have h0 := hcommon 0
        have h2 := hcommon 2
        rw [hH0 q] at h0
        rw [hH2 q] at h2
        dsimp only [offset]
        linear_combination h2 - h0
    · rintro ⟨hS, hq⟩
      refine ⟨shift q.1 + L0 q.1, hS, ?_⟩
      intro i
      fin_cases i
      · exact hH0 q
      · change H q 1 = shift q.1 + L0 q.1
        have hap := hAP q
        rw [hH0 q] at hap
        have h2 : H q 2 = shift q.1 + L0 q.1 := by
          rw [hH2 q]
          dsimp only [offset] at hq
          linear_combination hq
        rw [h2] at hap
        linear_combination hap
      · change H q 2 = shift q.1 + L0 q.1
        rw [hH2 q]
        dsimp only [offset] at hq
        linear_combination hq
  have hL0sum (w : I → ZMod p) :
      shift w + L0 w = ∑ x : I, c x * w x := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [I, c, shift, L0]
    ring
  have hset :
      Finset.univ.filter
          (fun q : (I → ZMod p) × ZMod p ↦
            ∃ s ∈ S, ∀ i : Fin 3, H q i = s) =
        Finset.univ.filter
          (fun q : (I → ZMod p) × ZMod p ↦
            (∑ x, c x * q.1 x) ∈ S ∧ q.2 = offset q.1) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hret q, hL0sum q.1]
  rw [hset]
  exact mme_ZMod_prime_linear_hash_affine_graph_fintype_card
    hcard c (Sum.inr ()) hc S offset


open BigOperators
open MME.StothersFourth.Phi125

set_option autoImplicit false
set_option warningAsError true

theorem phi125_hash_pair
    {p N alpha beta gamma : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hsum : alpha+beta+gamma=N)
    (e f : CyclicExactEdge N alpha beta gamma)
    (S : Finset (ZMod p)) (hne : e ≠ f) (shared : Fin 3)
    (hshared : cyclicModeWord e shared = cyclicModeWord f shared) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : (I → ZMod p) × ZMod p)
        (i : Fin 3) (a : CyclicExactEdge N alpha beta gamma) ↦
      cyclicAffineHash p N alpha beta gamma
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i a
    let retain := fun (q : (I → ZMod p) × ZMod p)
        (a : CyclicExactEdge N alpha beta gamma) ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i a = s
    ((Finset.univ.filter (fun q ↦ retain q e ∧ retain q f)).card) ≤
      p ^ (6 * N) := by
  classical
  dsimp only
  let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
  let weights := fun w : I → ZMod p ↦
    fun r j ↦ w (Sum.inl (r, j))
  let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
  let H := fun (q : (I → ZMod p) × ZMod p)
      (i : Fin 3) (a : CyclicExactEdge N alpha beta gamma) ↦
    cyclicAffineHash p N alpha beta gamma
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i a
  let retain := fun (q : (I → ZMod p) × ZMod p)
      (a : CyclicExactEdge N alpha beta gamma) ↦
    ∃ s ∈ S, ∀ i : Fin 3, H q i a = s
  let joint : ((I → ZMod p) × ZMod p) → Prop := fun q ↦
    retain q e ∧ retain q f
  change ((Finset.univ.filter joint).card) ≤ _
  have hcard : Fintype.card I = 6 * N + 1 := by
    simp [I]
    omega
  have hmodeNe : cyclicModeWord e ≠ cyclicModeWord f := by
    intro h
    exact hne (mme_stothers_phi125_cyclic_mode_word_tuple_injective N alpha beta gamma hsum h)
  obtain ⟨k, hk⟩ : ∃ k : Fin 3,
      cyclicModeWord e k ≠ cyclicModeWord f k := by
    by_contra h
    push Not at h
    exact hmodeNe (funext h)
  obtain ⟨r, j, hpivot⟩ :=
    mme_stothers_phi125_distinct_mode_code_difference_has_nonzero_coefficient
      (by omega : 5 ≤ p) k (cyclicModeWord e k) (cyclicModeWord f k) hk
  let c : I → ZMod p
    | Sum.inl x =>
        cyclicHashModeCode p N k (cyclicModeWord e k) x.1 x.2 -
          cyclicHashModeCode p N k (cyclicModeWord f k) x.1 x.2
    | Sum.inr _ => 0
  have hc : c (Sum.inl (r, j)) ≠ 0 := by
    simpa [c] using hpivot
  let L0 : (I → ZMod p) → ZMod p := fun w ↦
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cyclicHashModeCode p N 0 (cyclicModeWord e 0) r j *
        w (Sum.inl (r, j))
  let L2 : (I → ZMod p) → ZMod p := fun w ↦
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cyclicHashModeCode p N 2 (cyclicModeWord e 2) r j *
        w (Sum.inl (r, j))
  let offset : (I → ZMod p) → ZMod p := fun w ↦ L0 w - L2 w
  have h6 : (6 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 6 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hH0 (q : (I → ZMod p) × ZMod p) :
      H q 0 e = shift q.1 + L0 q.1 := by
    simpa [H, weights, shift, L0] using
      (mme_stothers_phi125_cyclic_affine_hash_normal_form
        (p := p) (N := N) (alpha := alpha) (beta := beta)
        (gamma := gamma) 
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) 0 e)
  have hH2 (q : (I → ZMod p) × ZMod p) :
      H q 2 e = shift q.1 + q.2 + L2 q.1 := by
    rw [show H q 2 e =
        shift q.1 + 6 * ((6 : ZMod p)⁻¹ * q.2) + L2 q.1 by
      simpa [H, weights, shift, L2] using
        (mme_stothers_phi125_cyclic_affine_hash_normal_form
          (p := p) (N := N) (alpha := alpha) (beta := beta)
          (gamma := gamma) 
          (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) 2 e)]
    rw [← mul_assoc, mul_inv_cancel₀ h6, one_mul]
  have hvertex (q : (I → ZMod p) × ZMod p)
      (a b : CyclicExactEdge N alpha beta gamma) (i : Fin 3)
      (hab : cyclicModeWord a i = cyclicModeWord b i) :
      H q i a = H q i b := by
    dsimp only [H]
    rw [mme_stothers_phi125_cyclic_affine_hash_normal_form
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i a]
    rw [mme_stothers_phi125_cyclic_affine_hash_normal_form
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i b]
    rw [hab]
  have hcsum (w : I → ZMod p) :
      (∑ x : I, c x * w x) =
        ∑ r : Fin 3, ∑ j : Fin (2 * N),
          (cyclicHashModeCode p N k (cyclicModeWord e k) r j -
            cyclicHashModeCode p N k (cyclicModeWord f k) r j) *
              w (Sum.inl (r, j)) := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [I, c]
  have hnormal (q : (I → ZMod p) × ZMod p)
      (hq : joint q) :
      (∑ x : I, c x * q.1 x) = 0 ∧ q.2 = offset q.1 := by
    rcases hq with ⟨⟨se, _hse, he⟩, ⟨sf, _hsf, hf⟩⟩
    have hlabel : se = sf := by
      have hv := hvertex q e f shared hshared
      rw [he shared, hf shared] at hv
      exact hv
    have hkhash : H q k e = H q k f := by
      exact (he k).trans (hlabel.trans (hf k).symm)
    constructor
    · rw [hcsum q.1]
      rw [← phi125_hash_difference
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) k e f]
      exact sub_eq_zero.mpr hkhash
    · have he20 : H q 2 e = H q 0 e :=
        (he 2).trans (he 0).symm
      rw [hH2 q, hH0 q] at he20
      dsimp only [offset]
      linear_combination he20
  exact mme_ZMod_prime_affine_joint_fintype_card_le
    hcard c (Sum.inl (r, j)) hc offset joint hnormal
end

section
open MME BigOperators
open MME.StothersFourth.Phi125
set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable local instance p125ExactFintype (N a b c : ℕ) : Fintype (ExactProfileWord N a b c) :=
  exactProfileWordFintype N a b c
noncomputable local instance p125EdgeFintype (N a b c : ℕ) : Fintype (CyclicExactEdge N a b c) :=
  cyclicExactEdgeFintype N a b c

theorem phi125_count_totals (N a b c : ℕ) (hsum : a+b+c=N) :
    ∑ r : Fin 6, profileMultiplicity a b c r = 2*N := by
  simp [Fin.sum_univ_succ,profileMultiplicity]
  omega

theorem phi125_marginal_totals (N a b c : ℕ) (hsum : a+b+c=N) (i : Fin 3) :
    ∑ s : Fin 5, marginalMultiplicity N a b c i s = 2*N := by
  fin_cases i <;> simp [Fin.sum_univ_succ,marginalMultiplicity] <;> omega

theorem phi125_cell_counts (N a b c : ℕ) (hsum : a+b+c=N) (i : Fin 3) (s : Fin 5) :
    ∑ r : {r : Fin 6 // pattern r i=s}, profileMultiplicity a b c r.1 =
      marginalMultiplicity N a b c i s := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun r : Fin 6 ↦ pattern r i=s))
    (by intro r; simp) (profileMultiplicity a b c)]
  rw [Finset.sum_filter]
  fin_cases i <;> fin_cases s <;>
    norm_num [Fin.sum_univ_succ,Fin.reduceFinMk,Fin.succ,profileMultiplicity,marginalMultiplicity,pattern] <;> norm_num [Fin.ext_iff] <;> omega

theorem phi125_exact_nonempty (N a b c : ℕ) (hsum : a+b+c=N) :
    Nonempty (ExactProfileWord N a b c) := by
  have hp : 0<Nat.card (ExactProfileWord N a b c) := by
    rw [mme_stothers_phi125_exact_profile_card N a b c hsum]
    have hh := Nat.multinomial_pos Finset.univ (profileMultiplicity a b c)
    simpa only [Nat.multinomial,phi125_count_totals N a b c hsum] using hh
  exact (Nat.card_pos_iff.mp hp).1

theorem phi125_supported_completion {N a b c : ℕ} (hsum : a+b+c=N)
    (x y z : ExactProfileWord N a b c) (hs : CoordinatewiseSupported x y z) :
    ∃ w : ExactProfileWord N a b c,
      modeWord w.1 0=modeWord x.1 0 ∧ modeWord w.1 1=modeWord y.1 1 ∧ modeWord w.1 2=modeWord z.1 2 := by
  classical
  choose w hw using hs
  have hm (i : Fin 3) : modeWord w i = modeWord ((![x,y,z] : Fin 3 → ExactProfileWord N a b c) i).1 i := by
    funext j
    fin_cases i
    · exact (hw j).1
    · exact (hw j).2.1
    · exact (hw j).2.2
  have hcounts : ∀ r : Fin 6, (Finset.univ.filter (fun j ↦ w j=r)).card=profileMultiplicity a b c r := by
    apply ((mme_stothers_phi125_exact_iff_marginal_profile N a b c hsum).2 w).mpr
    intro i s
    rw [hm i]
    exact ((mme_stothers_phi125_exact_iff_marginal_profile N a b c hsum).2
      ((![x,y,z] : Fin 3 → ExactProfileWord N a b c) i).1).mp
        ((![x,y,z] : Fin 3 → ExactProfileWord N a b c) i).2 i s
  exact ⟨⟨w,hcounts⟩,hm 0,hm 1,hm 2⟩

theorem phi125_cyclic_completion {N a b c : ℕ} (hsum : a+b+c=N)
    (x y z : CyclicExactEdge N a b c) (hs : CyclicCoordinatewiseSupported x y z) :
    ∃ e : CyclicExactEdge N a b c, cyclicModeWord e 0=cyclicModeWord x 0 ∧
      cyclicModeWord e 1=cyclicModeWord y 1 ∧ cyclicModeWord e 2=cyclicModeWord z 2 := by
  obtain ⟨u,hu0,hu1,hu2⟩ := phi125_supported_completion hsum x.1 y.1 z.1 hs.1
  obtain ⟨v,hv0,hv1,hv2⟩ := phi125_supported_completion hsum y.2.1 z.2.1 x.2.1 hs.2.1
  obtain ⟨w,hw0,hw1,hw2⟩ := phi125_supported_completion hsum z.2.2 x.2.2 y.2.2 hs.2.2
  exact ⟨(u,(v,w)),by simp only [cyclicModeWord,hu0,hv2,hw1]; rfl,
    by simp only [cyclicModeWord,hu1,hv0,hw2]; rfl,
    by simp only [cyclicModeWord,hu2,hv1,hw0]; rfl⟩

noncomputable def phi125_mode_degree (N a b c : ℕ) (i : Fin 3) : ℕ :=
  ∏ s : Fin 5, (marginalMultiplicity N a b c i s).factorial /
    ∏ r : {r : Fin 6 // pattern r i=s}, (profileMultiplicity a b c r.1).factorial

theorem phi125_mode_factorization (N a b c : ℕ) (hsum : a+b+c=N) (i : Fin 3) :
    Nat.card (ExactProfileWord N a b c) =
      ((2*N).factorial / ∏ s : Fin 5, (marginalMultiplicity N a b c i s).factorial) *
        phi125_mode_degree N a b c i := by
  classical
  let J := ∏ r : Fin 6, (profileMultiplicity a b c r).factorial
  let M := ∏ s : Fin 5, (marginalMultiplicity N a b c i s).factorial
  have hc (s : Fin 5) :
      (∏ r : {r : Fin 6 // pattern r i=s}, (profileMultiplicity a b c r.1).factorial) *
      ((marginalMultiplicity N a b c i s).factorial /
        ∏ r : {r : Fin 6 // pattern r i=s}, (profileMultiplicity a b c r.1).factorial) =
      (marginalMultiplicity N a b c i s).factorial := by
    have hh := Nat.multinomial_spec Finset.univ (fun r : {r : Fin 6 // pattern r i=s} ↦ profileMultiplicity a b c r.1)
    simpa only [Nat.multinomial,phi125_cell_counts N a b c hsum i s] using hh
  have hprod := congrArg (fun f : Fin 5 → ℕ ↦ ∏ s, f s) (funext hc)
  simp only [Finset.prod_mul_distrib] at hprod
  rw [Fintype.prod_fiberwise (fun r : Fin 6 ↦ pattern r i)
    (fun r ↦ (profileMultiplicity a b c r).factorial)] at hprod
  change J*phi125_mode_degree N a b c i=M at hprod
  have hrow := Nat.multinomial_spec Finset.univ (marginalMultiplicity N a b c i)
  simp only [Nat.multinomial,phi125_marginal_totals N a b c hsum i] at hrow
  have hjoint := Nat.multinomial_spec Finset.univ (profileMultiplicity a b c)
  simp only [Nat.multinomial,phi125_count_totals N a b c hsum] at hjoint
  rw [mme_stothers_phi125_exact_profile_card N a b c hsum]
  have hJ : 0<J := Finset.prod_pos (fun _ _ ↦ Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_left hJ
  change J*((2*N).factorial/J)=J*(((2*N).factorial/M)*phi125_mode_degree N a b c i)
  calc
    _ = (2*N).factorial := hjoint
    _ = M*((2*N).factorial/M) := hrow.symm
    _ = _ := by rw [← hprod]; ac_rfl
end

section
open MME BigOperators
open MME.StothersFourth.Phi125
set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable local instance p125FiniteExact (N a b c : ℕ) : Fintype (ExactProfileWord N a b c) :=
  exactProfileWordFintype N a b c
noncomputable local instance p125FiniteEdge (N a b c : ℕ) : Fintype (CyclicExactEdge N a b c) :=
  cyclicExactEdgeFintype N a b c

noncomputable def phi125_degree (N a b c : ℕ) : ℕ :=
  phi125_mode_degree N a b c 0*(phi125_mode_degree N a b c 1*phi125_mode_degree N a b c 2)

theorem phi125_hash_agrees_on_mode (p N a b c : ℕ)
    (w : Fin 3 → Fin (2*N) → ZMod p) (shift offset : ZMod p)
    (i : Fin 3) (e f : CyclicExactEdge N a b c)
    (h : cyclicModeWord e i=cyclicModeWord f i) :
    cyclicAffineHash p N a b c w shift offset i e=cyclicAffineHash p N a b c w shift offset i f := by
  rw [mme_stothers_phi125_cyclic_affine_hash_normal_form,
    mme_stothers_phi125_cyclic_affine_hash_normal_form,h]

theorem phi125_finite_hash_selection
    (N alpha beta gamma p : ℕ) (hN : 0 < N) (hsum : alpha + beta + gamma = N)
    [Fact p.Prime] (hp : 7 ≤ p) (S : Finset (ZMod p))
    (hfree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x+y=2*z → x=z ∧ z=y)
    (hlarge : 6 * ((phi125_degree N alpha beta gamma : ℕ) : ℝ) ≤ S.card) :
    ∃ kept : Finset (CyclicExactEdge N alpha beta gamma),
      ((∀ i : Fin 3, Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
        ∀ x y z : kept, CyclicCoordinatewiseSupported x.1 y.1 z.1 → x=y ∧ y=z) ∧
      (Fintype.card (CyclicExactEdge N alpha beta gamma) : ℝ) *
        ((S.card : ℝ) / (2 * (p : ℝ)^2)) ≤ kept.card := by
  classical
  let I := (Fin 3 × Fin (2*N)) ⊕ Unit
  let State := (I → ZMod p) × ZMod p
  let weights := fun w : I → ZMod p ↦ fun r j ↦ w (Sum.inl (r,j))
  let H := fun q : State ↦ cyclicAffineHash p N alpha beta gamma
    (weights q.1) (q.1 (Sum.inr ())) ((6 : ZMod p)⁻¹ * q.2)
  let retain := fun (q : State) (e : CyclicExactEdge N alpha beta gamma) ↦
    ∃ s ∈ S, ∀ i : Fin 3, H q i e = s
  let all : Finset (CyclicExactEdge N alpha beta gamma) := Finset.univ
  let D := phi125_degree N alpha beta gamma
  let ell : ℝ := (S.card : ℝ) / (2 * (p : ℝ)^2)
  have hp0 : 0 < p := by omega
  letI : NeZero p := ⟨by omega⟩
  have hstate : Fintype.card State = p^2 * p^(6*N) := by
    simp only [State, I, Fintype.card_prod, Fintype.card_fun, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_unit, ZMod.card]
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  have hdegree (i : Fin 3) (a : CyclicExactEdge N alpha beta gamma) (_ : a ∈ all) :
      (all.filter (fun b ↦ cyclicModeWord b i = cyclicModeWord a i)).card ≤ D := by
    have hh := mme_stothers_phi125_cyclic_mode_fiber_card N alpha beta gamma hsum a i
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,all,D,phi125_degree,phi125_mode_degree] using hh.le

  have hedge (a : CyclicExactEdge N alpha beta gamma) (_ : a ∈ all) :
      (Finset.univ.filter (fun q : State ↦ retain q a)).card = S.card * p^(6*N) :=
    phi125_hash_edge hp a S
  have hpair (ab : CyclicExactEdge N alpha beta gamma × CyclicExactEdge N alpha beta gamma)
      (hab : ab ∈ ((all ×ˢ all).filter (fun ab ↦ ab.1 ≠ ab.2 ∧
        ∃ i : Fin 3, cyclicModeWord ab.1 i = cyclicModeWord ab.2 i))) :
      (Finset.univ.filter (fun q : State ↦ retain q ab.1 ∧ retain q ab.2)).card ≤ p^(6*N) := by
    obtain ⟨_, hne, i, hi⟩ := Finset.mem_filter.mp hab
    exact phi125_hash_pair hp hsum ab.1 ab.2 S hne i hi
  have hclosure (q : State)
      (x : CyclicExactEdge N alpha beta gamma) (hx : x ∈ all.filter (retain q))
      (y : CyclicExactEdge N alpha beta gamma) (hy : y ∈ all.filter (retain q))
      (z : CyclicExactEdge N alpha beta gamma) (hz : z ∈ all.filter (retain q))
      (hs : CyclicCoordinatewiseSupported x y z) :
      ∃ e ∈ all.filter (retain q), cyclicModeWord e 0 = cyclicModeWord x 0 ∧
        cyclicModeWord e 1 = cyclicModeWord y 1 ∧
        cyclicModeWord e 2 = cyclicModeWord z 2 := by
    obtain ⟨sx, hsx, hx'⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨sy, hsy, hy'⟩ := (Finset.mem_filter.mp hy).2
    obtain ⟨sz, hsz, hz'⟩ := (Finset.mem_filter.mp hz).2
    have hap := mme_stothers_phi125_cyclic_affine_hash_AP (weights q.1) (q.1 (Sum.inr ())) ((6 : ZMod p)⁻¹*q.2) x y z hs
    change H q 0 x + H q 1 y = 2 * H q 2 z at hap
    rw [hx', hy', hz'] at hap
    obtain ⟨hxs, hsy'⟩ := hfree sx hsx sy hsy sz hsz hap
    obtain ⟨e, he0, he1, he2⟩ := phi125_cyclic_completion hsum x y z hs
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he0, he1, he2⟩
    refine ⟨sz, hsz, ?_⟩
    intro i
    fin_cases i
    · exact (phi125_hash_agrees_on_mode _ _ _ _ _ _ _ _ _ _ _ he0).trans ((hx' 0).trans hxs)
    · exact (phi125_hash_agrees_on_mode _ _ _ _ _ _ _ _ _ _ _ he1).trans ((hy' 1).trans hsy'.symm)
    · exact (phi125_hash_agrees_on_mode _ _ _ _ _ _ _ _ _ _ _ he2).trans (hz' 2)
  have hmargin : ((p^2 : ℕ) : ℝ)*ell + 3*(D : ℝ)*(1 : ℝ) ≤ S.card := by
    dsimp [ell, D]
    push_cast
    have hp' : (p : ℝ) ≠ 0 := by positivity
    have heq : (p : ℝ)^2 * ((S.card : ℝ) / (2 * (p : ℝ)^2)) = (S.card : ℝ)/2 := by field_simp
    rw [heq]
    have hlarge' := hlarge
    push_cast at hlarge'
    nlinarith only [hlarge']
  obtain ⟨q, kept, _, hmode, hdiag, hcard⟩ :=
    mme_type2_fractional_retention_of_relative_mode_degree
      (fun i e ↦ cyclicModeWord e i) CyclicCoordinatewiseSupported
      all all retain (p^2) S.card (p^(6*N)) D 1 (all.card : ℝ) (D : ℝ) ell
      (by positivity) hstate (by simp) hdegree (by simp) hedge hpair
      (by rfl) hclosure (by simpa only [Nat.cast_one] using hmargin)
  exact ⟨kept, ⟨hmode,hdiag⟩, by simpa only [all, Finset.card_univ, ell] using hcard⟩
end

section
open MME BigOperators MME.StothersFourth.Phi125
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable local instance p125BoundsExact (N a b c : ℕ) : Fintype (ExactProfileWord N a b c) := exactProfileWordFintype N a b c
noncomputable local instance p125BoundsEdge (N a b c : ℕ) : Fintype (CyclicExactEdge N a b c) := cyclicExactEdgeFintype N a b c

theorem phi125_degree_bounds (N a b c : ℕ) (hsum : a+b+c=N) :
    1≤phi125_degree N a b c ∧ phi125_degree N a b c≤5^(12*N) := by
  classical
  obtain ⟨w⟩ := phi125_exact_nonempty N a b c hsum
  let e : CyclicExactEdge N a b c := (w,w,w)
  let F := {f : CyclicExactEdge N a b c // cyclicModeWord f 0=cyclicModeWord e 0}
  have heq : Nat.card F=phi125_degree N a b c :=
    mme_stothers_phi125_cyclic_mode_fiber_card N a b c hsum e 0
  have hpos : 0<Nat.card F := (Nat.card_pos_iff).mpr ⟨⟨⟨e,rfl⟩⟩,inferInstance⟩
  have hle : Nat.card F≤Nat.card (CyclicExactEdge N a b c) := by
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hw : Nat.card (ExactProfileWord N a b c)≤6^(2*N) := by
    calc
      _ ≤ Nat.card (ProfileWord N) := by
        rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
        exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = _ := by simp [ProfileWord,Nat.card_eq_fintype_card]
  have hc : Nat.card (CyclicExactEdge N a b c)=(Nat.card (ExactProfileWord N a b c))^3 := by
    simp [CyclicExactEdge,Nat.card_prod,pow_succ];ring
  refine ⟨by omega,?_⟩
  rw [← heq]
  calc
    _ ≤ Nat.card (CyclicExactEdge N a b c) := hle
    _ ≤ (6^(2*N))^3 := by rw [hc]; exact Nat.pow_le_pow_left hw 3
    _ = 6^(6*N) := by rw [← pow_mul];congr 1;omega
    _ ≤ 25^(6*N) := Nat.pow_le_pow_left (by omega) _
    _ = 5^(12*N) := by rw [show (25 : ℕ)=5^2 by norm_num,← pow_mul];congr 1;omega

theorem phi125_prime_parameters (N a b c : ℕ) (hsum : a+b+c=N) :
    ∃ p : ℕ, Nat.Prime p ∧ 7≤p ∧ ∃ S : Finset (ZMod p),
      (∀ x∈S,∀ y∈S,∀ z∈S,x+y=2*z → x=z ∧ z=y) ∧
      6*(phi125_degree N a b c : ℝ)≤S.card ∧
      (p : ℝ)≤(phi125_degree N a b c : ℝ)*Real.exp (2000*Real.sqrt ((12*N+1 : ℕ) : ℝ)) := by
  classical
  let D := phi125_degree N a b c
  obtain ⟨hD1,hD5⟩ := phi125_degree_bounds N a b c hsum
  obtain ⟨p,hp,hp5,S,hSr,hSf,hSbig,hpbound⟩ :=
    mme_prime_behrend_dominates_bounded_collision_degree (12*N) D hD1 hD5
  have hcard := Finset.card_le_card hSr
  rw [Finset.card_range] at hcard
  have hScard : 6*D≤S.card := by exact_mod_cast hSbig
  have hp7 : 7≤p := by omega
  obtain ⟨hcastcard,hcastfree⟩ := mme_stothers_phi233_lower_half_cast_label_package p S hSr hSf
  exact ⟨p,hp,hp7,S.image (fun s : ℕ ↦ (s : ZMod p)),hcastfree,
    by simpa only [hcastcard] using hSbig,hpbound⟩

theorem phi125_capacity_identity (N a b c : ℕ) (hsum : a+b+c=N) :
    (∏ i : Fin 3, Nat.multinomial Finset.univ (marginalMultiplicity N a b c i))*
      phi125_degree N a b c = (Nat.card (ExactProfileWord N a b c))^3 := by
  have h0 := phi125_mode_factorization N a b c hsum 0
  have h1 := phi125_mode_factorization N a b c hsum 1
  have h2 := phi125_mode_factorization N a b c hsum 2
  simp only [Nat.multinomial,phi125_marginal_totals N a b c hsum]
  rw [Fin.prod_univ_three]
  unfold phi125_degree
  calc
    _ = (((2*N).factorial/∏ s : Fin 5,(marginalMultiplicity N a b c 0 s).factorial)*phi125_mode_degree N a b c 0)*
      (((2*N).factorial/∏ s : Fin 5,(marginalMultiplicity N a b c 1 s).factorial)*phi125_mode_degree N a b c 1)*
      (((2*N).factorial/∏ s : Fin 5,(marginalMultiplicity N a b c 2 s).factorial)*phi125_mode_degree N a b c 2) := by ring
    _ = _ := by rw [← h0,← h1,← h2];ring
end

section
open MME Real BigOperators Filter MME.StothersFourth.Phi125
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

noncomputable def phi125_entropy (a b c : ℝ) : ℝ :=
  Real.log 2+2*Real.negMulLog ((a+c)/2)+Real.negMulLog b+
    2*Real.negMulLog (a/2)+2*Real.negMulLog ((b+c)/2)

theorem phi125_multinomial_entropy (w : Fin 5 → ℕ) (n : ℕ) (hn : 0<n) (hsum : ∑ i,w i=n) :
    Real.exp ((n : ℝ)*∑ i,Real.negMulLog ((w i : ℝ)/n))≤
      (6*((n+1 : ℕ) : ℝ))^5*(Nat.multinomial Finset.univ w : ℝ) := by
  have h := mme_dwz_multinomial_entropy_polynomial_lower w 1 (by omega) (show 0<∑ i,w i by omega)
  have hlog : Real.log 2≠0 := (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne'
  simp only [hsum,Nat.mul_one,mul_one,one_mul,mme_modern_entropyBits,Fintype.card_fin] at h
  have he (x : ℝ) : (n : ℝ)*Real.log 2*(x/Real.log 2)=n*x := by field_simp
  rw [he] at h
  simpa only [Nat.cast_one,one_mul] using h

theorem phi125_capacity_entropy (N a b c : ℕ) (hN : 0<N) (hsum : a+b+c=N) :
    Real.exp ((2*N : ℝ)*phi125_entropy (a/N) (b/N) (c/N))≤
      (6*((2*N+1 : ℕ) : ℝ))^15*
      ((Nat.card (ExactProfileWord N a b c) : ℝ)^3/(phi125_degree N a b c : ℝ)) := by
  have hh (i : Fin 3) := phi125_multinomial_entropy (marginalMultiplicity N a b c i)
    (2*N) (by omega) (phi125_marginal_totals N a b c hsum i)
  have hprod := Finset.prod_le_prod (fun i (_ : i∈(Finset.univ : Finset (Fin 3))) ↦ (Real.exp_pos _).le)
    (fun i (_ : i∈(Finset.univ : Finset (Fin 3))) ↦ hh i)
  rw [← Real.exp_sum] at hprod
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hprod
  have hD : (phi125_degree N a b c : ℝ)≠0 := by
    have hh := (phi125_degree_bounds N a b c hsum).1
    exact_mod_cast (show phi125_degree N a b c≠0 by omega)
  have hid := congrArg (fun x : ℕ ↦ (x : ℝ)) (phi125_capacity_identity N a b c hsum)
  push_cast at hid
  have hratio : (∏ i : Fin 3,(Nat.multinomial Finset.univ (marginalMultiplicity N a b c i) : ℝ))=
      (Nat.card (ExactProfileWord N a b c) : ℝ)^3/(phi125_degree N a b c : ℝ) :=
    (eq_div_iff hD).mpr hid
  rw [hratio] at hprod
  have hn0 : (N : ℝ)≠0 := by positivity
  have hhalf : (N : ℝ)/(2*N)=1/2 := by field_simp
  have henthalf : Real.negMulLog (1/2)=Real.log 2/2 := by norm_num [Real.negMulLog,Real.log_div];ring
  have hsumE : (∑ i : Fin 3,(2*N : ℝ)*∑ s : Fin 5,
      Real.negMulLog ((marginalMultiplicity N a b c i s : ℝ)/(2*N)))=
      (2*N : ℝ)*phi125_entropy (a/N) (b/N) (c/N) := by
    simp only [Fin.sum_univ_succ]
    norm_num [Fin.succ,marginalMultiplicity]
    rw [hhalf,henthalf]
    have hab : ((a : ℝ)+c)/(2*N)=((a/N)+(c/N))/2 := by ring
    have hbc : ((b : ℝ)+c)/(2*N)=((b/N)+(c/N))/2 := by ring
    have ha : (a : ℝ)/(2*N)=(a/N)/2 := by ring
    have hb : (2*b : ℝ)/(2*N)=b/N := by ring
    rw [hab,hbc,ha,hb]
    unfold phi125_entropy
    ring
  push_cast at hprod
  rw [hsumE] at hprod
  simpa only [← pow_mul,Nat.reduceMul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hprod

theorem phi125_entropy_rate_identity (a b L E H : ℝ)
    (ha : 0<a) (hb : 0<b) (hab : a+b≤1) (hL : 0<L) (hE : 0<E) (hH : 0<H) :
    phi125_entropy a b (1-a-b)+(a+b)*Real.log L+(1-a)*Real.log E+(1-a-b)*Real.log H =
      Real.log (4/H*((L/a)^a*((E*H)/(1-a))^(1-a))*
        ((L/b)^b*((2*H)/(1-b))^(1-b))) := by
  have ha1 : 0<1-a := by linarith
  have hb1 : 0<1-b := by linarith
  have h2 : (2 : ℝ)≠0 := by norm_num
  have h4 : (4 : ℝ)≠0 := by norm_num
  have hlog4 : Real.log 4=2*Real.log 2 := by rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow];norm_num
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_div h4 hH.ne',Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity : 0<L/a),Real.log_rpow (by positivity : 0<E*H/(1-a)),
    Real.log_rpow (by positivity : 0<L/b),Real.log_rpow (by positivity : 0<2*H/(1-b)),
    Real.log_div hL.ne' ha.ne',Real.log_div (mul_pos hE hH).ne' ha1.ne',
    Real.log_div hL.ne' hb.ne',Real.log_div (by positivity) hb1.ne',
    Real.log_mul hE.ne' hH.ne',Real.log_mul h2 hH.ne',hlog4]
  unfold phi125_entropy
  rw [show a+(1-a-b)=1-b by ring,show b+(1-a-b)=1-a by ring]
  simp only [Real.negMulLog]
  rw [Real.log_div hb1.ne' h2,Real.log_div ha.ne' h2,Real.log_div ha1.ne' h2]
  ring
end

section
open Real BigOperators Filter
set_option autoImplicit false
theorem phi125_scaled_log_limit (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ Real.log (s * n + 1) / (2 * n)) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ ↦ s * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop hs)
  have hl := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ht
  have hr : Tendsto (fun n : ℕ ↦ (s * n + 1) / (2 * n)) atTop (nhds (s / 2)) := by
    have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hh := ((tendsto_const_nhds (x := s)).add hi).div_const (2 : ℝ)
    convert hh.congr' ?_ using 1
    · simp
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp
  have hh := hl.mul hr
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < s * (n : ℝ) + 1 := by positivity
    simp only [Function.comp_apply, pow_one, one_mul, add_zero]
    field_simp

theorem phi125_scaled_sqrt_limit (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ Real.sqrt (s * n + 1) / (2 * n)) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ ↦ s * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop hs)
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp ht)
  have hr : Tendsto (fun n : ℕ ↦ (s * n + 1) / (2 * n)) atTop (nhds (s / 2)) := by
    have hin : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hh := ((tendsto_const_nhds (x := s)).add hin).div_const (2 : ℝ)
    convert hh.congr' ?_ using 1
    · simp
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp
  have hh := hi.mul hr
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < s * (n : ℝ) + 1 := by positivity
    have hsqrt : Real.sqrt (s * n + 1) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    simp only [Function.comp_apply]
    field_simp
    nlinarith [Real.sq_sqrt hpos.le]


theorem phi125_penalty_limit :
    Tendsto (fun n : ℕ ↦ (15*Real.log (6*((2*n+1 : ℕ) : ℝ)) +
      4000*Real.sqrt ((12*n+1 : ℕ) : ℝ)) / (2*n)) atTop (nhds 0) := by
  have hl := phi125_scaled_log_limit 2 (by norm_num)
  have hs := phi125_scaled_sqrt_limit 12 (by norm_num)
  have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := ((((hi.const_mul (Real.log 6)).div_const 2).add hl).const_mul 15 |>.add
    (hs.const_mul 4000))
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hp : (2*(n : ℝ)+1) ≠ 0 := by positivity
    push_cast
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hp]
    ring
end

section
open MME Real BigOperators Filter MME.StothersFourth.Phi125
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem phi125_profile_surplus (L E H a b V : ℝ)
    (hL : 0<L) (hE : 0<E) (hH : 0<H) (ha : 0<a) (hb : 0<b) (hab : a+b≤1) (hV : 0<V)
    (hVlt : V<4/H*((L/a)^a*((E*H)/(1-a))^(1-a))*((L/b)^b*((2*H)/(1-b))^(1-b))) :
    ∃ N alpha beta gamma : ℕ, 0<N ∧ alpha+beta+gamma=N ∧
      V^(2*N)*(phi125_degree N alpha beta gamma : ℝ)*Real.exp (4000*Real.sqrt ((12*N+1 : ℕ) : ℝ)) <
      (Nat.card (ExactProfileWord N alpha beta gamma) : ℝ)^3*
        (L^(2*alpha+2*beta)*E^(2*beta+2*gamma)*H^(2*gamma)) := by
  let A := fun n : ℕ ↦ Nat.floor (a*(n : ℝ))
  let B := fun n : ℕ ↦ Nat.floor (b*(n : ℝ))
  let C := fun n : ℕ ↦ n-(A n+B n)
  have hABn (n : ℕ) : A n+B n≤n := by
    have hfa := Nat.floor_le (show 0≤a*(n : ℝ) by positivity)
    have hfb := Nat.floor_le (show 0≤b*(n : ℝ) by positivity)
    have hh : (A n : ℝ)+(B n : ℝ)≤n := by dsimp [A,B]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact_mod_cast hh
  have hsum (n : ℕ) : A n+B n+C n=n := Nat.add_sub_of_le (hABn n)
  have hA : Tendsto (fun n : ℕ ↦ (A n : ℝ)/(n : ℝ)) atTop (nhds a) :=
    (tendsto_nat_floor_mul_div_atTop ha.le).comp tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun n : ℕ ↦ (B n : ℝ)/(n : ℝ)) atTop (nhds b) :=
    (tendsto_nat_floor_mul_div_atTop hb.le).comp tendsto_natCast_atTop_atTop
  have hC : Tendsto (fun n : ℕ ↦ (C n : ℝ)/(n : ℝ)) atTop (nhds (1-a-b)) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub hA).sub hB
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ)≠0 := by positivity
    dsimp [C]
    rw [Nat.cast_sub (hABn n),Nat.cast_add]
    field_simp
    <;> ring
  let rate := fun n ↦ phi125_entropy (A n/n) (B n/n) (C n/n)+
    ((A n/n)+(B n/n))*Real.log L+((B n/n)+(C n/n))*Real.log E+(C n/n)*Real.log H
  have hneg {f : ℕ → ℝ} {x : ℝ} (h : Tendsto f atTop (nhds x)) :
      Tendsto (fun n ↦ Real.negMulLog (f n)) atTop (nhds (Real.negMulLog x)) :=
    Real.continuous_negMulLog.continuousAt.tendsto.comp h
  have hent : Tendsto (fun n ↦ phi125_entropy (A n/n) (B n/n) (C n/n)) atTop
      (nhds (phi125_entropy a b (1-a-b))) :=
    (((tendsto_const_nhds.add ((hneg ((hA.add hC).div_const 2)).const_mul 2)).add (hneg hB)).add
      ((hneg (hA.div_const 2)).const_mul 2)).add ((hneg ((hB.add hC).div_const 2)).const_mul 2)
  have hrate := ((hent.add ((hA.add hB).mul_const (Real.log L))).add
    ((hB.add hC).mul_const (Real.log E))).add (hC.mul_const (Real.log H))
  rw [show b+(1-a-b)=1-a by ring,phi125_entropy_rate_identity a b L E H ha hb hab hL hE hH] at hrate
  have hlim := hrate.sub phi125_penalty_limit
  have hlog := Real.log_lt_log hV hVlt
  have hevent := hlim.eventually (eventually_gt_nhds (by simpa only [sub_zero] using hlog))
  obtain ⟨N,hN,hgap⟩ := ((eventually_gt_atTop 0).and hevent).exists
  let alpha := A N
  let beta := B N
  let gamma := C N
  let P : ℝ := 6*((2*N+1 : ℕ) : ℝ)
  let Q : ℝ := ((12*N+1 : ℕ) : ℝ)
  let D : ℝ := (phi125_degree N alpha beta gamma : ℝ)
  let T : ℝ := (Nat.card (ExactProfileWord N alpha beta gamma) : ℝ)^3
  let J := L^(2*alpha+2*beta)*E^(2*beta+2*gamma)*H^(2*gamma)
  have hD : 0<D := by
    have hh := (phi125_degree_bounds N alpha beta gamma (hsum N)).1
    dsimp [D]
    exact_mod_cast (show 0<phi125_degree N alpha beta gamma by omega)
  have hP : 0<P := by dsimp [P]; positivity
  have hJ : 0<J := by dsimp [J]; positivity
  have hf := mul_le_mul_of_nonneg_right (phi125_capacity_entropy N alpha beta gamma hN (hsum N)) hJ.le
  have hlogJ : Real.log J=(2*N : ℝ)*
      (((alpha/N)+(beta/N))*Real.log L+((beta/N)+(gamma/N))*Real.log E+(gamma/N)*Real.log H) := by
    dsimp [J]
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
      Real.log_pow,Real.log_pow,Real.log_pow]
    push_cast
    have hn0 : (N : ℝ)≠0 := by positivity
    field_simp
    <;> ring
  have hleft : Real.exp ((2*N : ℝ)*phi125_entropy (alpha/N) (beta/N) (gamma/N))*J=
      Real.exp ((2*N : ℝ)*rate N) := by
    rw [← Real.exp_log hJ,← Real.exp_add,hlogJ]
    congr 1
    dsimp [rate,alpha,beta,gamma]
    ring
  rw [hleft] at hf
  have hngap : (2*N : ℝ)*Real.log V+15*Real.log P+4000*Real.sqrt Q<(2*N : ℝ)*rate N := by
    have hh := mul_lt_mul_of_pos_left hgap (by positivity : (0 : ℝ)<2*N)
    change (2*N : ℝ)*Real.log V<(2*N : ℝ)*(rate N-(15*Real.log P+4000*Real.sqrt Q)/(2*N)) at hh
    have hn0 : (N : ℝ)≠0 := by positivity
    field_simp at hh
    nlinarith only [hh]
  have heq : (2*N : ℝ)*Real.log V+15*Real.log P+4000*Real.sqrt Q=
      Real.log (V^(2*N)*P^15*Real.exp (4000*Real.sqrt Q)) := by
    conv_rhs => rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,Real.log_exp]
    push_cast
    ring
  have hh := (Real.exp_lt_exp.mpr hngap).trans_le hf
  rw [heq,Real.exp_log (by positivity)] at hh
  change V^(2*N)*P^15*Real.exp (4000*Real.sqrt Q)<P^15*(T/D)*J at hh
  have hc : V^(2*N)*Real.exp (4000*Real.sqrt Q)<(T/D)*J := by
    have hp15 : 0<P^15 := by positivity
    nlinarith only [hh,hp15]
  have hc' := mul_lt_mul_of_pos_right hc hD
  refine ⟨N,alpha,beta,gamma,hN,hsum N,?_⟩
  change V^(2*N)*D*Real.exp (4000*Real.sqrt Q)<T*J
  field_simp at hc'
  nlinarith only [hc']
end

section
open MME BigOperators MME.StothersFourth.Phi125
set_option autoImplicit false
set_option maxHeartbeats 200000
theorem phi125_cyclic_mixed_supported
    {K : Type u} [Field K] {N alpha beta gamma : ℕ}
    (x y z : CyclicExactEdge N alpha beta gamma)
    (hnz : ∀ j, (mmeCyclicTripleGrading (outerGrading K 6)).blockTensor
      (fun i ↦ phi125_cyclic_address (![x,y,z] i) i j) ≠ 0) :
    CyclicCoordinatewiseSupported x y z := by
  have hh (j : Fin (2*N)) :
      (fun i ↦ phi125_cyclic_address (![x,y,z] i) i j) =
      mmeCyclicTripleGrade
        (fun s ↦ modeWord ((![x.1,y.1,z.1] : Fin 3 → ExactProfileWord N alpha beta gamma) s).1 s j)
        (fun s ↦ modeWord ((![y.2.1,z.2.1,x.2.1] : Fin 3 → ExactProfileWord N alpha beta gamma) s).1 s j)
        (fun s ↦ modeWord ((![z.2.2,x.2.2,y.2.2] : Fin 3 → ExactProfileWord N alpha beta gamma) s).1 s j) := by
    funext i
    fin_cases i <;> rfl
  have hparts (j : Fin (2*N)) := mme_cyclic_triple_grading_nonzero_factors
    (outerGrading K 6) _ _ _ (by rw [← hh j]; exact hnz j)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    obtain ⟨r,hr⟩ := phi125_outer_grading_support 6 _ (hparts j).1
    exact ⟨r,congrFun hr.symm 0,congrFun hr.symm 1,congrFun hr.symm 2⟩
  · intro j
    obtain ⟨r,hr⟩ := phi125_outer_grading_support 6 _ (hparts j).2.1
    exact ⟨r,congrFun hr.symm 0,congrFun hr.symm 1,congrFun hr.symm 2⟩
  · intro j
    obtain ⟨r,hr⟩ := phi125_outer_grading_support 6 _ (hparts j).2.2
    exact ⟨r,congrFun hr.symm 0,congrFun hr.symm 1,congrFun hr.symm 2⟩

theorem phi125_induced_profile_restrict
    {K : Type u} [Field K] {N alpha beta gamma : ℕ} (hsum : alpha+beta+gamma=N)
    (kept : Finset (CyclicExactEdge N alpha beta gamma))
    (hdiag : ∀ x y z : kept, CyclicCoordinatewiseSupported x.1 y.1 z.1 → x=y ∧ y=z) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin kept.card ↦
        cyclicSymmetrization (TensorObj.kronFin 6 (fun r ↦
          (componentObj K 6 r).kronPow (profileMultiplicity alpha beta gamma r)))))
      ((cyclicSymmetrization (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow (2*N)) := by
  classical
  let A := fun j : Fin kept.card ↦ phi125_cyclic_address (kept.equivFin.symm j).1
  have hind (js : Fin 3 → Fin kept.card)
      (hnz : ∀ r, (mmeCyclicTripleGrading (outerGrading K 6)).blockTensor
        (fun i ↦ A (js i) i r) ≠ 0) : ∃ j, js = fun _ ↦ j := by
    let es := fun i ↦ kept.equivFin.symm (js i)
    have hs := phi125_cyclic_mixed_supported (K := K) (es 0).1 (es 1).1 (es 2).1 (by
      intro j
      have he : (![(es 0).1, (es 1).1, (es 2).1] : Fin 3 → CyclicExactEdge N alpha beta gamma) =
          fun i ↦ (es i).1 := by funext i; fin_cases i <;> rfl
      rw [he]
      exact hnz j)
    obtain ⟨h01,h12⟩ := hdiag (es 0) (es 1) (es 2) hs
    have hj01 : js 0 = js 1 := kept.equivFin.symm.injective h01
    have hj12 : js 1 = js 2 := kept.equivFin.symm.injective h12
    refine ⟨js 0, ?_⟩
    funext i
    fin_cases i <;> simp_all
  have hh := mme_induced_graded_address_blocks_restrict
    (mmeCyclicTripleGrading (outerGrading K 6)) A hind
  refine TensorObj.Restrict.trans (mme_bigAdd_mono_restrict ?_) hh
  intro j
  exact phi125_cyclic_product_restrict 6 (kept.equivFin.symm j).1
end

section
open MME BigOperators Filter MME.StothersFourth.Phi125
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem phi125_value_downward {K : Type u} [Field K]
    (T : TensorObj K 3) (tau B V : ℝ) (h : HasTauValueAtLeast T tau B)
    (hV : 0≤V) (hVB : V≤B) : HasTauValueAtLeast T tau V := by
  refine ⟨hV, ?_⟩
  intro eps heps
  apply (h.2 eps heps).mono
  rintro N ⟨k,a,b,c,hr,hbound⟩
  refine ⟨k,a,b,c,hr,?_⟩
  by_cases heps1 : eps≤1
  · exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hV hVB _) (by linarith)).trans hbound
  · exact (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hV _) (by linarith)).trans
      (Finset.sum_nonneg (fun _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _))

noncomputable def phi125_endpoint (tau : ℝ) : Fin 6 → ℝ :=
  ![MME.StothersFourth.L 6 tau,MME.StothersFourth.E 6 tau*MME.StothersFourth.L 6 tau,
    MME.StothersFourth.E 6 tau*MME.StothersFourth.H 6 tau,
    MME.StothersFourth.E 6 tau*MME.StothersFourth.H 6 tau,
    MME.StothersFourth.E 6 tau*MME.StothersFourth.L 6 tau,MME.StothersFourth.L 6 tau]

theorem phi125_endpoint_pos (tau : ℝ) (r : Fin 6) : 0<phi125_endpoint tau r := by
  fin_cases r <;> simp [phi125_endpoint,MME.StothersFourth.L,MME.StothersFourth.E,MME.StothersFourth.H] <;> positivity

theorem phi125_component_value {K : Type u} [Field K] (tau : ℝ) (htau : 2≤3*tau)
    (r : Fin 6) (V : ℝ) (hV : 0≤V) (hVB : V<phi125_endpoint tau r) :
    HasTauValueAtLeast (cyclicSymmetrization (componentObj K 6 r)) tau V := by
  have hE : 0<MME.StothersFourth.E 6 tau := by unfold MME.StothersFourth.E; positivity
  have hL : 0<MME.StothersFourth.L 6 tau := by unfold MME.StothersFourth.L; positivity
  have hEH : 0<MME.StothersFourth.E 6 tau*MME.StothersFourth.H 6 tau := by
    unfold MME.StothersFourth.E MME.StothersFourth.H; positivity
  have heE : ((((1*1*12)*(1*1*12)*(1*1*12) : ℕ) : ℝ)^tau)=MME.StothersFourth.E 6 tau := by
    norm_num [MME.StothersFourth.E]
    rw [show (1728 : ℝ)=12^3 by norm_num,← Real.rpow_natCast_mul (by norm_num : (0 : ℝ)≤12) 3 tau]
    norm_num
  have heEH : ((((12*1*38)*(12*1*38)*(12*1*38) : ℕ) : ℝ)^tau)=
      MME.StothersFourth.E 6 tau*MME.StothersFourth.H 6 tau := by
    norm_num only [Nat.reduceMul,Nat.cast_ofNat,MME.StothersFourth.E,MME.StothersFourth.H]
    rw [show (94818816 : ℝ)=(12*38)^3 by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ)≤12*38) 3 tau]
    norm_num only [Nat.cast_ofNat]
    simpa only [show (12 : ℝ)*38=456 by norm_num] using
      (Real.mul_rpow (by norm_num : (0 : ℝ)≤12) (by norm_num : (0 : ℝ)≤38) (z := 3*tau))
  have hvE := heE ▸ mme_MMObj_cyclic_tau_value (K := K) 1 1 12 tau
  have hvEH := heEH ▸ mme_MMObj_cyclic_tau_value (K := K) 12 1 38 tau
  have hMM (W : ℝ) (hW : 0≤W) (hWB : W<MME.StothersFourth.E 6 tau) :
      HasTauValueAtLeast (cyclicSymmetrization (MMObj K 1 1 12)) tau W :=
    phi125_value_downward _ _ _ _ hvE hW hWB.le
  have hCoupled (W : ℝ) (hW : 0≤W) (hWB : W<MME.StothersFourth.L 6 tau) :
      HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau W :=
    mme_CW_q6_coupled_raw_cyclic_value_below tau htau W hW hWB
  have hRot (W : ℝ) (hW : 0≤W) (hWB : W<MME.StothersFourth.L 6 tau) :
      HasTauValueAtLeast (cyclicSymmetrization (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6))) tau W :=
    mme_HasTauValueAtLeast_mono_restrict
      (mme_cyclicSymmetrization_isomorphic_cyclic_orbit (coupledObj K 6)).2.2 (hCoupled W hW hWB)
  fin_cases r
  · exact hRot V hV hVB
  · exact mme_cyclic_kron_two_strict_below_product _ _ tau _ _ hE hL hMM hCoupled V hV hVB
  · exact phi125_value_downward _ _ _ _ hvEH hV hVB.le
  · exact phi125_value_downward _ _ _ _ hvEH hV hVB.le
  · apply mme_cyclic_kron_two_strict_below_product _ _ tau _ _ hL hE hCoupled hMM V hV
    simpa [phi125_endpoint, mul_comm] using hVB
  · exact hRot V hV hVB

theorem phi125_profile_value {K : Type u} [Field K] (tau : ℝ) (htau : 2≤3*tau)
    (a b c : ℕ) (W : ℝ) (hW : 0≤W)
    (hWB : W < MME.StothersFourth.L 6 tau^(2*a+2*b)*
      MME.StothersFourth.E 6 tau^(2*b+2*c)*MME.StothersFourth.H 6 tau^(2*c)) :
    HasTauValueAtLeast (cyclicSymmetrization (TensorObj.kronFin 6 (fun r ↦
      (componentObj K 6 r).kronPow (profileMultiplicity a b c r)))) tau W := by
  apply mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
    (componentObj K 6) (profileMultiplicity a b c) tau (phi125_endpoint tau)
    (phi125_endpoint_pos tau) (phi125_component_value tau htau) W hW
  convert hWB using 1
  simp [Fin.prod_univ_succ,Fin.succ,phi125_endpoint,profileMultiplicity,mul_pow,pow_add,pow_mul]
  ring
end

section
open MME BigOperators Filter MME.StothersFourth.Phi125
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
theorem phi125_weighted_retention_bound
    (P D F S C M B V : ℝ)
    (hP : 0 < P) (hD : 0 < D) (hF : 0 < F)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hprime : P ≤ D * F)
    (hlabels : 6 * D ≤ S)
    (hkept : C * (S / (2 * P ^ 2)) ≤ M)
    (hbudget : V * D * F ^ 2 < C * B) :
    V < M * B := by
  have hp2 : 0 < 2 * P ^ 2 := by positivity
  have hcount : C * S ≤ M * (2 * P ^ 2) := by
    apply (div_le_iff₀ hp2).mp
    simpa only [mul_div_assoc] using hkept
  have hleft : 6 * D * C ≤ M * (2 * P ^ 2) := by
    have := mul_le_mul_of_nonneg_left hlabels hC
    nlinarith
  have hsq : P ^ 2 ≤ (D * F) ^ 2 :=
    pow_le_pow_left₀ hP.le hprime 2
  have hright : M * (2 * P ^ 2) ≤ M * (2 * (D * F) ^ 2) := by
    gcongr
  have hboth := hleft.trans hright
  have hmargin : C ≤ M * (D * F ^ 2) := by
    nlinarith [mul_pos hD hF]
  have hweighted := mul_le_mul_of_nonneg_right hmargin hB
  have hpos : 0 < D * F ^ 2 := by positivity
  apply (mul_lt_mul_iff_left₀ hpos).mp
  nlinarith

theorem solution
    {K : Type u} [Field K] (tau a b : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V <
        4 / MME.StothersFourth.H 6 tau *
          ((MME.StothersFourth.L 6 tau / a) ^ a *
            ((MME.StothersFourth.E 6 tau *
              MME.StothersFourth.H 6 tau) / (1 - a)) ^ (1 - a)) *
          ((MME.StothersFourth.L 6 tau / b) ^ b *
            ((2 * MME.StothersFourth.H 6 tau) / (1 - b)) ^
              (1 - b))) :
    ∃ (N alpha beta gamma : ℕ),
      0 < N ∧ alpha + beta + gamma = N ∧
      ∃ (kept : Finset
          (MME.StothersFourth.Phi125.CyclicExactEdge
            N alpha beta gamma))
        (block : kept → TensorObj K 3) (B : ℝ),
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦
            MME.StothersFourth.Phi125.cyclicModeWord e.1 i)) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j : Fin kept.card ↦
            block (kept.equivFin.symm j)))
          ((cyclicSymmetrization
            (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
              (2 * N)) ∧
        0 ≤ B ∧
        (∀ e : kept, ∀ W : ℝ,
          0 ≤ W → W < B → HasTauValueAtLeast (block e) tau W) ∧
        V ^ (2 * N) < (kept.card : ℝ) * B := by

  classical
  let L := MME.StothersFourth.L 6 tau
  let E := MME.StothersFourth.E 6 tau
  let H := MME.StothersFourth.H 6 tau
  let Z := 4/H*((L/a)^a*((E*H)/(1-a))^(1-a))*((L/b)^b*((2*H)/(1-b))^(1-b))
  let U := (V+Z)/2
  have hVU : V<U := by dsimp [U,Z,L,E,H];linarith
  have hU : 0<U := lt_of_le_of_lt hV hVU
  have hUZ : U<Z := by dsimp [U,Z,L,E,H];linarith
  have hL : 0<L := by unfold L MME.StothersFourth.L;positivity
  have hE : 0<E := by unfold E MME.StothersFourth.E;positivity
  have hH : 0<H := by unfold H MME.StothersFourth.H;positivity
  obtain ⟨N,alpha,beta,gamma,hN,hsum,hsurplus⟩ :=
    phi125_profile_surplus L E H a b U hL hE hH ha hb hab hU hUZ
  let D : ℝ := (phi125_degree N alpha beta gamma : ℝ)
  let F := Real.exp (2000*Real.sqrt ((12*N+1 : ℕ) : ℝ))
  let C : ℝ := (Nat.card (ExactProfileWord N alpha beta gamma) : ℝ)^3
  let B := L^(2*alpha+2*beta)*E^(2*beta+2*gamma)*H^(2*gamma)
  have hD : 0<D := by
    have hh := (phi125_degree_bounds N alpha beta gamma hsum).1
    dsimp [D]
    exact_mod_cast (show 0<phi125_degree N alpha beta gamma by omega)
  have hF : 0<F := Real.exp_pos _
  have hB : 0<B := by dsimp [B];positivity
  obtain ⟨p,hp,hp7,S,hfree,hlarge,hpbound⟩ := phi125_prime_parameters N alpha beta gamma hsum
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨kept,⟨hmode,hdiag⟩,hcount⟩ := phi125_finite_hash_selection N alpha beta gamma p hN hsum hp7 S hfree hlarge
  letI : Fintype (ExactProfileWord N alpha beta gamma) := exactProfileWordFintype N alpha beta gamma
  letI : Fintype (CyclicExactEdge N alpha beta gamma) := cyclicExactEdgeFintype N alpha beta gamma
  have hcard : (Fintype.card (CyclicExactEdge N alpha beta gamma) : ℝ)=C := by
    rw [← Nat.card_eq_fintype_card]
    dsimp [CyclicExactEdge,C]
    rw [Nat.card_prod,Nat.card_prod]
    push_cast
    ring
  rw [hcard] at hcount
  have hFsq : F^2=Real.exp (4000*Real.sqrt ((12*N+1 : ℕ) : ℝ)) := by
    dsimp [F]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hstrict : V^(2*N)*D*F^2<C*B := by
    rw [hFsq]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hV hVU.le (2*N)) hD.le)
      (Real.exp_pos (4000*Real.sqrt ((12*N+1 : ℕ) : ℝ))).le
    exact hh.trans_lt hsurplus
  have hVB : V^(2*N)<(kept.card : ℝ)*B :=
    phi125_weighted_retention_bound (p : ℝ) D F S.card C kept.card B (V^(2*N))
      (by exact_mod_cast hp.pos) hD hF (by dsimp [C];positivity) (by positivity) hB.le
      hpbound hlarge hcount hstrict
  refine ⟨N,alpha,beta,gamma,hN,hsum,kept,
    (fun _ ↦ cyclicSymmetrization (TensorObj.kronFin 6 (fun r ↦
      (componentObj K 6 r).kronPow (profileMultiplicity alpha beta gamma r)))),B,
    hmode,phi125_induced_profile_restrict hsum kept hdiag,hB.le,?_,hVB⟩
  intro e W hW hWB
  exact phi125_profile_value tau htauLower alpha beta gamma W hW hWB
end
