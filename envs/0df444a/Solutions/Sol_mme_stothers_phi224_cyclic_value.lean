-- Prove2me | solution 1 for mme_stothers_phi224_cyclic_value
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T21:05:31.669715+00:00
-- url     : https://prove2.me/submissions/1ba84a07-96be-41a9-998d-04fba089db94

import Theorems.Thm_mme_CW_fourth_tensor_eq_sum_literal_terms
import Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_CW_square_canonical_coupled112_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled121_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled211_restrict
import Theorems.Thm_mme_CW_square_canonical_elementary_blocks
import Theorems.Thm_mme_HasTauValueAtLeast_bigAdd_uniform_strict
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
import Theorems.Thm_mme_MMObj_cyclic_tau_value
import Theorems.Thm_mme_ZMod_prime_affine_joint_fintype_card_le
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_cyclicSymmetrization_isomorphic_cyclic_orbit
import Theorems.Thm_mme_cyclic_grading_address_block_iso
import Theorems.Thm_mme_cyclic_kron_two_strict_below_product
import Theorems.Thm_mme_cyclic_triple_grading_nonzero_factors
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso
import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree
import Theorems.Thm_mme_stothers_phi125_distinct_mode_code_difference_has_nonzero_coefficient
import Theorems.Thm_mme_stothers_phi233_lower_half_cast_label_package
import Theorems.Thm_mme_stothers_q6_EHL_optimizer_regime
import Theorems.Thm_mme_type2_fractional_retention_of_relative_mode_degree

/- Provenance: current-environment direct closure of the earlier phi224 proof
chain.  It replaces the old target proof's route through
`mme_stothers_lemma51_remaining_four_values`, which returns to phi224, with an
explicit finite block construction. -/

universe u

set_option warningAsError true
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

section
namespace MME.StothersFourth.Phi224
set_option autoImplicit false
set_option maxRecDepth 10000
def pattern (r : Fin 9) (i : Fin 3) : Fin 5 :=
  match r.val,i.val with
  | 0,0 => 0
  | 0,1 => 0
  | 0,2 => 4
  | 1,0 => 0
  | 1,1 => 1
  | 1,2 => 3
  | 2,0 => 0
  | 2,1 => 2
  | 2,2 => 2
  | 3,0 => 1
  | 3,1 => 0
  | 3,2 => 3
  | 4,0 => 1
  | 4,1 => 1
  | 4,2 => 2
  | 5,0 => 1
  | 5,1 => 2
  | 5,2 => 1
  | 6,0 => 2
  | 6,1 => 0
  | 6,2 => 2
  | 7,0 => 2
  | 7,1 => 1
  | 7,2 => 1
  | 8,0 => 2
  | 8,1 => 2
  | 8,2 => 0
  | _,_ => 0

def profileMultiplicity (alpha beta gamma delta : ℕ) (r : Fin 9) : ℕ :=
  match r.val with
  | 0 => alpha
  | 1 => beta
  | 2 => gamma
  | 3 => beta
  | 4 => 2*delta
  | 5 => beta
  | 6 => gamma
  | 7 => beta
  | _ => alpha

def marginalMultiplicity (N alpha beta gamma delta : ℕ) (i : Fin 3) (s : Fin 5) : ℕ :=
  match i.val,s.val with
  | 0,0 => alpha+beta+gamma
  | 0,1 => 2*beta+2*delta
  | 0,2 => alpha+beta+gamma
  | 0,3 => 0
  | 0,4 => 0
  | 1,0 => alpha+beta+gamma
  | 1,1 => 2*beta+2*delta
  | 1,2 => alpha+beta+gamma
  | 1,3 => 0
  | 1,4 => 0
  | 2,0 => alpha
  | 2,1 => 2*beta
  | 2,2 => 2*gamma+2*delta
  | 2,3 => 2*beta
  | 2,4 => alpha
  | _,_ => 0

abbrev ProfileWord (N : ℕ) := Fin (2 * N) → Fin 9

/-- Projection of a six-label word to one of its three grade words. -/
def modeWord {N : ℕ} (w : ProfileWord N) (i : Fin 3) : Fin (2 * N) → Fin 5 :=
  fun j => pattern (w j) i

/-- The exact symmetric profile used for the `phi_125` laser extraction. -/
def SymmetricProfileWord (N alpha beta gamma delta : ℕ) : Type :=
  {w : ProfileWord N //
    ∀ r : Fin 9,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card = profileMultiplicity alpha beta gamma delta r}

/-- The ambient family obtained by remembering only the three mode
marginals of the exact profile. -/
def MarginalProfileWord (N alpha beta gamma delta : ℕ) : Type :=
  {w : ProfileWord N //
    ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => modeWord w i j = s)).card =
          marginalMultiplicity N alpha beta gamma delta i s}

abbrev ExactProfileWord := MarginalProfileWord

/-- Three cyclic copies of one exact profile, the edge set used before
type-2 hashing. -/
def CyclicExactEdge (N alpha beta gamma delta : ℕ) : Type :=
  ExactProfileWord N alpha beta gamma delta ×
    (ExactProfileWord N alpha beta gamma delta ×
      ExactProfileWord N alpha beta gamma delta)

/-- One vertex of a cyclic edge consists of one mode word from each cyclic
orientation. -/
def CyclicModeWord (N : ℕ) : Type :=
  (Fin (2 * N) → Fin 5) ×
    ((Fin (2 * N) → Fin 5) × (Fin (2 * N) → Fin 5))

/-- The actual three vertices of a cyclic exact edge. -/
def cyclicModeWord
    {N alpha beta gamma delta : ℕ}
    (e : CyclicExactEdge N alpha beta gamma delta) :
    Fin 3 → CyclicModeWord N
  | ⟨0, _⟩ => (modeWord e.1.1 0, (modeWord e.2.1.1 2, modeWord e.2.2.1 1))
  | ⟨1, _⟩ => (modeWord e.1.1 1, (modeWord e.2.1.1 0, modeWord e.2.2.1 2))
  | ⟨2, _⟩ => (modeWord e.1.1 2, (modeWord e.2.1.1 1, modeWord e.2.2.1 0))
  | ⟨_ + 3, h⟩ => absurd h (by omega)

end MME.StothersFourth.Phi224

namespace MME.StothersFourth.Phi224

set_option autoImplicit false

def CoordinatewiseSupported
    {N alpha beta gamma delta : ℕ}
    (x y z : ExactProfileWord N alpha beta gamma delta) : Prop :=
  ∀ j : Fin (2 * N), ∃ r : Fin 9,
    pattern r 0 = modeWord x.1 0 j ∧
    pattern r 1 = modeWord y.1 1 j ∧
    pattern r 2 = modeWord z.1 2 j

def CyclicCoordinatewiseSupported
    {N alpha beta gamma delta : ℕ}
    (x y z : CyclicExactEdge N alpha beta gamma delta) : Prop :=
  CoordinatewiseSupported x.1 y.1 z.1 ∧
    CoordinatewiseSupported y.2.1 z.2.1 x.2.1 ∧
    CoordinatewiseSupported z.2.2 x.2.2 y.2.2

abbrev cyclicHashModeCode
    (p N : ℕ) (i : Fin 3) (u : CyclicModeWord N) :
    Fin 3 → Fin (2 * N) → ZMod p :=
  MME.StothersFourth.Phi233.cyclicHashModeCode p N i u

def cyclicAffineHash
    (p N alpha beta gamma delta : ℕ)
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e : CyclicExactEdge N alpha beta gamma delta) : ZMod p :=
  shift + match i with
  | ⟨0, _⟩ =>
      Phi233.doubledXHash (2 * offset) (w 0) (modeWord e.1.1 0) +
        4 * Phi233.doubledZHash 0 (w 1) (modeWord e.2.1.1 2) -
        2 * Phi233.doubledYHash offset (w 2) (modeWord e.2.2.1 1)
  | ⟨1, _⟩ =>
      Phi233.doubledYHash (2 * offset) (w 0) (modeWord e.1.1 1) -
        2 * Phi233.doubledXHash 0 (w 1) (modeWord e.2.1.1 0) +
        4 * Phi233.doubledZHash offset (w 2) (modeWord e.2.2.1 2)
  | ⟨2, _⟩ =>
      Phi233.doubledZHash (2 * offset) (w 0) (modeWord e.1.1 2) +
        Phi233.doubledYHash 0 (w 1) (modeWord e.2.1.1 1) +
        Phi233.doubledXHash offset (w 2) (modeWord e.2.2.1 0)
  | ⟨r + 3, h⟩ => absurd h (by omega)

noncomputable def exactProfileWordFintype
    (N alpha beta gamma delta : ℕ) :
    Fintype (ExactProfileWord N alpha beta gamma delta) :=
  @Subtype.fintype _ _ (Classical.decPred _) Pi.instFintype

noncomputable def cyclicExactEdgeFintype
    (N alpha beta gamma delta : ℕ) :
    Fintype (CyclicExactEdge N alpha beta gamma delta) := by
  letI := exactProfileWordFintype N alpha beta gamma delta
  unfold CyclicExactEdge
  infer_instance

noncomputable def targetFinset
    (N alpha beta gamma delta : ℕ) :
    Finset (CyclicExactEdge N alpha beta gamma delta) := by
  letI := cyclicExactEdgeFintype N alpha beta gamma delta
  exact Finset.univ

end MME.StothersFourth.Phi224
end

section
open MME Module


namespace MME.StothersFourth.Phi224

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- The fixed coarse grade of the three mode spaces of `phi_125`. -/
def modeTotalGrade (s : Fin 3) : Fin 9 :=
  cwFourthBlockType 2 2 4 s

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
    Basis (ModeIndex q s) K ((cwFourthConstituent K q 2 2 4).V s) := by
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
    (cwFourthConstituent K q 2 2 4).TypeGrading 5 where
  decomp s := cwBasisGrade (canonicalBasis K q s) (outerGrade q s)
  is_internal s := cwBasisGrade_isInternal (canonicalBasis K q s) (outerGrade q s)

end MME.StothersFourth.Phi224
end

section
open MME TensorProduct Module


namespace MME.StothersFourth.Phi224

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem p224_fb_canonical_basis_mem_grade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {iota kappa : Type*} [DecidableEq kappa]
    (b : Basis iota K V) (g : iota → kappa) (i : iota) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private theorem p224_fb_square_basis_mem_own_grade
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : Fin (q + 2) × Fin (q + 2)) :
    cwSquareCanonicalBasis K q s p ∈
      (cwSquareCanonicalGrading K q).classOf s
        (cwSquarePairGrade q p) := by
  exact Submodule.subset_span ⟨p, rfl, rfl⟩

private theorem p224_fb_fourth_basis_apply
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    cwFourthCanonicalBasis K q s p =
      cwSquareCanonicalBasis K q s p.1 ⊗ₜ[K]
        cwSquareCanonicalBasis K q s p.2 := by
  unfold cwFourthCanonicalBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

private theorem p224_fb_fourth_basis_mem_own_fine_grade
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
      p224_fb_square_basis_mem_own_grade K q s p.1⟩ ⊗ₜ[K]
    ⟨cwSquareCanonicalBasis K q s p.2,
      p224_fb_square_basis_mem_own_grade K q s p.2⟩
  have hz := TensorObj.TypeGrading.classKronEmbed_mem
    G G s (cwSquarePairGrade q p.1) (cwSquarePairGrade q p.2) z
  have heq :
      cwFourthCanonicalBasis K q s p =
        TensorObj.TypeGrading.classKronEmbed
          G G s (cwSquarePairGrade q p.1) (cwSquarePairGrade q p.2) z := by
    rw [p224_fb_fourth_basis_apply]
    rfl
  rw [heq]
  change
    TensorObj.TypeGrading.classKronEmbed
        G G s (cwSquarePairGrade q p.1) (cwSquarePairGrade q p.2) z ∈
      (TensorObj.TypeGrading.kronGrading G G).classOf s
        (finProdFinEquiv
          (cwSquarePairGrade q p.1, cwSquarePairGrade q p.2))
  exact hz

private theorem p224_fb_fine_pair_mem_coarse
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
private theorem p224_fb_outerGrade_eq_iff_fine_pair
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

private theorem p224_fb_outer_blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin 5)
    (p : ModeIndex q s) :
    (outerGrading K q).blockProj s a (canonicalBasis K q s p) =
      if h : outerGrade q s p = a then
        ⟨canonicalBasis K q s p, by
          change canonicalBasis K q s p ∈
            cwBasisGrade (canonicalBasis K q s) (outerGrade q s) a
          simpa only [h] using p224_fb_canonical_basis_mem_grade
            (canonicalBasis K q s) (outerGrade q s) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (outerGrading K q) s (outerGrade q s p) _
      (p224_fb_canonical_basis_mem_grade
        (canonicalBasis K q s) (outerGrade q s) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (outerGrading K q) s a (outerGrade q s p) (Ne.symm h) _
      (p224_fb_canonical_basis_mem_grade
        (canonicalBasis K q s) (outerGrade q s) p)

private theorem p224_fb_outer_class_le_fine_comap
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
  have hm := p224_fb_fourth_basis_mem_own_fine_grade K q s p.1
  obtain ⟨hx, hy⟩ := (p224_fb_outerGrade_eq_iff_fine_pair q sx sy hsum s p).mp hp
  simpa only [hx, hy] using hm

/-- Canonical inclusion of one outer mode block into its literal fine block. -/
private noncomputable def p224_fb_outerClassToFine
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
    (fun x => p224_fb_outer_class_le_fine_comap K q sx sy hsum s x.property)

@[simp] private theorem outerClassToFine_coe
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) (x : (outerGrading K q).classOf s (sx s)) :
    (p224_fb_outerClassToFine K q sx sy hsum s x).val = x.1.1 := by
  rfl

private theorem p224_fb_coarse_blockProj_fourth_basis
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
      simpa only [h] using p224_fb_canonical_basis_mem_grade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K q) s (modeTotalGrade s)
      (cwFourthPairGrade q p) (Ne.symm h) _
      (p224_fb_canonical_basis_mem_grade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)

private theorem p224_fb_fine_blockProj_fourth_basis
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
            p224_fb_fourth_basis_mem_own_fine_grade K q s p⟩
      else 0 := by
  let G := TensorObj.TypeGrading.kronGrading
    (cwSquareCanonicalGrading K q) (cwSquareCanonicalGrading K q)
  let own := finProdFinEquiv
    (cwSquarePairGrade q p.1, cwSquarePairGrade q p.2)
  have hp : cwFourthCanonicalBasis K q s p ∈ G.classOf s own :=
    p224_fb_fourth_basis_mem_own_fine_grade K q s p
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

private theorem p224_fb_outerFine_projection_comp
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) :
    (p224_fb_outerClassToFine K q sx sy hsum s).comp
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
  · have hcproj := p224_fb_coarse_blockProj_fourth_basis K q s p
    rw [dif_pos hc] at hcproj
    let pc : ModeIndex q s := ⟨p, hc⟩
    have hcstep := congrArg (fun x =>
      p224_fb_outerClassToFine K q sx sy hsum s
        ((outerGrading K q).blockProj s (sx s) x)) hcproj
    by_cases ho : outerGrade q s pc = sx s
    · have hoproj := p224_fb_outer_blockProj_basis K q s (sx s) pc
      rw [dif_pos ho] at hoproj
      have hfine := (p224_fb_outerGrade_eq_iff_fine_pair q sx sy hsum s pc).mp ho
      change cwSquarePairGrade q p.1 = sx s ∧
        cwSquarePairGrade q p.2 = sy s at hfine
      have hfproj := p224_fb_fine_blockProj_fourth_basis K q s sx sy p
      rw [dif_pos hfine] at hfproj
      calc
        _ = p224_fb_outerClassToFine K q sx sy hsum s
              ((outerGrading K q).blockProj s (sx s)
                (canonicalBasis K q s pc)) := hcstep
        _ = p224_fb_outerClassToFine K q sx sy hsum s
              ⟨canonicalBasis K q s pc, by
                change canonicalBasis K q s pc ∈
                  cwBasisGrade (canonicalBasis K q s)
                    (outerGrade q s) (sx s)
                simpa only [ho] using p224_fb_canonical_basis_mem_grade
                  (canonicalBasis K q s) (outerGrade q s) pc⟩ :=
            congrArg (p224_fb_outerClassToFine K q sx sy hsum s) hoproj
        _ = ⟨cwFourthCanonicalBasis K q s p, by
              change cwFourthCanonicalBasis K q s p ∈
                (TensorObj.TypeGrading.kronGrading
                  (cwSquareCanonicalGrading K q)
                  (cwSquareCanonicalGrading K q)).classOf s
                    (finProdFinEquiv (sx s, sy s))
              simpa only [hfine.1, hfine.2] using
                p224_fb_fourth_basis_mem_own_fine_grade K q s p⟩ := by
            apply Subtype.ext
            exact canonicalBasis_coe K q s pc
        _ = _ := hfproj.symm
    · have hoproj := p224_fb_outer_blockProj_basis K q s (sx s) pc
      rw [dif_neg ho] at hoproj
      have hfine : ¬(cwSquarePairGrade q p.1 = sx s ∧
          cwSquarePairGrade q p.2 = sy s) := by
        intro hp
        exact ho ((p224_fb_outerGrade_eq_iff_fine_pair q sx sy hsum s pc).mpr hp)
      have hfproj := p224_fb_fine_blockProj_fourth_basis K q s sx sy p
      rw [dif_neg hfine] at hfproj
      calc
        _ = p224_fb_outerClassToFine K q sx sy hsum s
              ((outerGrading K q).blockProj s (sx s)
                (canonicalBasis K q s pc)) := hcstep
        _ = p224_fb_outerClassToFine K q sx sy hsum s 0 :=
          congrArg (p224_fb_outerClassToFine K q sx sy hsum s) hoproj
        _ = 0 := map_zero _
        _ = _ := hfproj.symm
  · have hcproj := p224_fb_coarse_blockProj_fourth_basis K q s p
    rw [dif_neg hc] at hcproj
    have hfine : ¬(cwSquarePairGrade q p.1 = sx s ∧
        cwSquarePairGrade q p.2 = sy s) := by
      intro hp
      exact hc (p224_fb_fine_pair_mem_coarse q sx sy hsum s p hp)
    have hfproj := p224_fb_fine_blockProj_fourth_basis K q s sx sy p
    rw [dif_neg hfine] at hfproj
    calc
      _ = p224_fb_outerClassToFine K q sx sy hsum s
            ((outerGrading K q).blockProj s (sx s) 0) :=
          congrArg (fun x =>
            p224_fb_outerClassToFine K q sx sy hsum s
              ((outerGrading K q).blockProj s (sx s) x)) hcproj
      _ = 0 := by simp only [map_zero]
      _ = _ := hfproj.symm

private theorem p224_fb_piTensorMap_three
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
  refine ⟨fun s => p224_fb_outerClassToFine K q sx sy hsum s, ?_⟩
  change PiTensorProduct.map
      (fun s => p224_fb_outerClassToFine K q sx sy hsum s)
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
          ((p224_fb_outerClassToFine K q sx sy hsum s).comp
            ((outerGrading K q).blockProj s (sx s))).comp
              ((cwFourthCanonicalGrading K q).blockProj s
                (modeTotalGrade s))) (cwFourthObj K q).t :=
      p224_fb_piTensorMap_three
        (fun s => p224_fb_outerClassToFine K q sx sy hsum s)
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
        (p224_fb_outerFine_projection_comp K q sx sy hsum s) x

end MME.StothersFourth.Phi224

open MME.StothersFourth.Phi224

set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

theorem phi224_fine_block_restrict_outer_block
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

namespace MME.StothersFourth.Phi224

private theorem p224_support_basis_mem_cwBasisGrade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι κ : Type*} [DecidableEq κ]
    (b : Basis ι K V) (g : ι -> κ) (i : ι) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private def p224_support_cwVec
    (K : Type u) [Field K] (q : Nat) (s : Fin 3) (a : Fin (q + 2)) :
    CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => (Pi.single a 1 : Fin (q + 2) -> K)
  | ⟨1, _⟩ => (Pi.single a 1 : Fin (q + 2) -> K)
  | ⟨2, _⟩ => (Pi.single a 1 : Fin (q + 2) -> K)

private theorem p224_support_literalTermMonomial_eq_tprod
    (K : Type u) [Field K] (q : Nat)
    (t : CWLiteralTerm q) :
    cwLiteralTermMonomial K q t =
      PiTensorProduct.tprod K
        (fun s => p224_support_cwVec K q s (cwLiteralTermTriple q t s)) := by
  unfold cwLiteralTermMonomial CWMonom
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem p224_support_squareCanonicalBasis_apply
    (K : Type u) [Field K] (q : Nat) (s : Fin 3)
    (a b : Fin (q + 2)) :
    cwSquareCanonicalBasis K q s (a, b) =
      p224_support_cwVec K q s a ⊗ₜ[K] p224_support_cwVec K q s b := by
  letI : IsScalarTower K K (Fin (q + 2) -> K) :=
    IsScalarTower.of_algebraMap_smul (by simp)
  fin_cases s <;>
    change (Module.Basis.tensorProduct (R := K) (S := K)
      (Pi.basisFun K (Fin (q + 2)))
      (Pi.basisFun K (Fin (q + 2)))) (a, b) = _ <;>
    rw [Module.Basis.tensorProduct_apply] <;>
    simp [p224_support_cwVec, Pi.basisFun_apply]

private theorem p224_support_fourthCanonicalBasis_apply
    (K : Type u) [Field K] (q : Nat) (s : Fin 3)
    (p :
      (Fin (q + 2) × Fin (q + 2)) ×
        (Fin (q + 2) × Fin (q + 2))) :
    cwFourthCanonicalBasis K q s p =
      cwSquareCanonicalBasis K q s p.1 ⊗ₜ[K]
        cwSquareCanonicalBasis K q s p.2 := by
  unfold cwFourthCanonicalBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

private theorem p224_support_interchange_tprod
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

private theorem p224_support_fourLiteralTerms_eq_basis_tprod
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
  rw [p224_support_literalTermMonomial_eq_tprod, p224_support_literalTermMonomial_eq_tprod,
    p224_support_literalTermMonomial_eq_tprod, p224_support_literalTermMonomial_eq_tprod,
    p224_support_interchange_tprod, p224_support_interchange_tprod, p224_support_interchange_tprod]
  congr 1
  funext s
  rw [p224_support_fourthCanonicalBasis_apply,
    p224_support_squareCanonicalBasis_apply, p224_support_squareCanonicalBasis_apply]
  rfl

private theorem p224_support_coarse_blockProj_fourth_basis
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
      simpa only [h] using p224_support_basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K q) s (modeTotalGrade s)
      (cwFourthPairGrade q p) (Ne.symm h) _
      (p224_support_basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)

private theorem p224_support_outer_blockProj_basis
    (K : Type u) [Field K] (q : Nat) (s : Fin 3) (a : Fin 5)
    (p : ModeIndex q s) :
    (outerGrading K q).blockProj s a (canonicalBasis K q s p) =
      if h : outerGrade q s p = a then
        ⟨canonicalBasis K q s p, by
          change canonicalBasis K q s p ∈
            cwBasisGrade (canonicalBasis K q s) (outerGrade q s) a
          simpa only [h] using p224_support_basis_mem_cwBasisGrade
            (canonicalBasis K q s) (outerGrade q s) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (outerGrading K q) s (outerGrade q s p) _
      (p224_support_basis_mem_cwBasisGrade
        (canonicalBasis K q s) (outerGrade q s) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (outerGrading K q) s a (outerGrade q s p) (Ne.symm h) _
      (p224_support_basis_mem_cwBasisGrade
        (canonicalBasis K q s) (outerGrade q s) p)

private theorem p224_support_coordGrade_zero (q : Nat) :
    cwSquareCoordGrade q (cwZeroIndex q) = 0 := by
  simp [cwSquareCoordGrade, cwZeroIndex]

private theorem p224_support_coordGrade_middle (q : Nat) (i : Fin q) :
    cwSquareCoordGrade q (cwMiddleIndex q i) = 1 := by
  simp [cwSquareCoordGrade, cwMiddleIndex]
  omega

private theorem p224_support_coordGrade_top (q : Nat) :
    cwSquareCoordGrade q (cwTopIndex q) = 2 := by
  simp [cwSquareCoordGrade, cwTopIndex]

private theorem p224_support_literalTerm_grade_sum_two
    (q : Nat) (t : CWLiteralTerm q) :
    (cwSquareCoordGrade q (cwLiteralTermTriple q t 0)).val +
      (cwSquareCoordGrade q (cwLiteralTermTriple q t 1)).val +
      (cwSquareCoordGrade q (cwLiteralTermTriple q t 2)).val = 2 := by
  rcases t with ⟨i, r⟩ | r <;> fin_cases r <;>
    simp [cwLiteralTermTriple, p224_support_coordGrade_zero,
      p224_support_coordGrade_middle, p224_support_coordGrade_top]

private def p224_support_firstSquareType (q : Nat)
    (t₁ t₂ : CWLiteralTerm q) (s : Fin 3) : Fin 5 :=
  cwSquarePairGrade q
    (cwLiteralTermTriple q t₁ s, cwLiteralTermTriple q t₂ s)

private def p224_support_secondSquareType (q : Nat)
    (t₃ t₄ : CWLiteralTerm q) (s : Fin 3) : Fin 5 :=
  cwSquarePairGrade q
    (cwLiteralTermTriple q t₃ s, cwLiteralTermTriple q t₄ s)

private theorem p224_support_firstSquareType_grade_sum_four
    (q : Nat) (t₁ t₂ : CWLiteralTerm q) :
    (p224_support_firstSquareType q t₁ t₂ 0).val +
      (p224_support_firstSquareType q t₁ t₂ 1).val +
      (p224_support_firstSquareType q t₁ t₂ 2).val = 4 := by
  have h₁ := p224_support_literalTerm_grade_sum_two q t₁
  have h₂ := p224_support_literalTerm_grade_sum_two q t₂
  simp only [p224_support_firstSquareType, cwSquarePairGrade]
  omega

private theorem p224_support_secondSquareType_grade_sum_four
    (q : Nat) (t₃ t₄ : CWLiteralTerm q) :
    (p224_support_secondSquareType q t₃ t₄ 0).val +
      (p224_support_secondSquareType q t₃ t₄ 1).val +
      (p224_support_secondSquareType q t₃ t₄ 2).val = 4 := by
  have h₃ := p224_support_literalTerm_grade_sum_two q t₃
  have h₄ := p224_support_literalTerm_grade_sum_two q t₄
  simp only [p224_support_secondSquareType, cwSquarePairGrade]
  omega

private theorem p224_support_fourLiteralTerms_outer_pattern
    (q : Nat) (t₁ t₂ t₃ t₄ : CWLiteralTerm q)
    (hcoarse : ∀ s,
      cwFourthPairGrade q (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s) =
        modeTotalGrade s) :
    ∃ r : Fin 9,
      (fun s => p224_support_firstSquareType q t₁ t₂ s) = pattern r := by
  have hfirst := p224_support_firstSquareType_grade_sum_four q t₁ t₂
  have hsecond := p224_support_secondSquareType_grade_sum_four q t₃ t₄
  have hiVal := congrArg Fin.val (hcoarse 0)
  have hjVal := congrArg Fin.val (hcoarse 1)
  have hkVal := congrArg Fin.val (hcoarse 2)
  have hi : (p224_support_firstSquareType q t₁ t₂ 0).val +
      (p224_support_secondSquareType q t₃ t₄ 0).val = 2 := by
    simpa [p224_support_firstSquareType, p224_support_secondSquareType, cwFourthPairGrade,
      cwFourthIndexOfLiteralTerms, modeTotalGrade, cwFourthBlockType] using hiVal
  have hj : (p224_support_firstSquareType q t₁ t₂ 1).val +
      (p224_support_secondSquareType q t₃ t₄ 1).val = 2 := by
    simpa [p224_support_firstSquareType, p224_support_secondSquareType, cwFourthPairGrade,
      cwFourthIndexOfLiteralTerms, modeTotalGrade, cwFourthBlockType] using hjVal
  have hk : (p224_support_firstSquareType q t₁ t₂ 2).val +
      (p224_support_secondSquareType q t₃ t₄ 2).val = 4 := by
    simpa [p224_support_firstSquareType, p224_support_secondSquareType, cwFourthPairGrade,
      cwFourthIndexOfLiteralTerms, modeTotalGrade, cwFourthBlockType] using hkVal
  have hclass (i j k : Fin 5) (hs : i.val+j.val+k.val=4) (hi : i.val≤2) (hj : j.val≤2) :
      ∃ r : Fin 9, pattern r 0=i ∧ pattern r 1=j ∧ pattern r 2=k := by
    interval_cases hival : i.val <;> interval_cases hjval : j.val
    · refine ⟨0,?_,?_,?_⟩ <;> apply Fin.ext <;> norm_num [pattern] <;> omega
    · refine ⟨1,?_,?_,?_⟩ <;> apply Fin.ext <;> norm_num [pattern] <;> omega
    · refine ⟨2,?_,?_,?_⟩ <;> apply Fin.ext <;> norm_num [pattern] <;> omega
    · refine ⟨3,?_,?_,?_⟩ <;> apply Fin.ext <;> norm_num [pattern] <;> omega
    · refine ⟨4,?_,?_,?_⟩ <;> apply Fin.ext <;> norm_num [pattern] <;> omega
    · refine ⟨5,?_,?_,?_⟩ <;> apply Fin.ext <;> norm_num [pattern] <;> omega
    · refine ⟨6,?_,?_,?_⟩ <;> apply Fin.ext <;> norm_num [pattern] <;> omega
    · refine ⟨7,?_,?_,?_⟩ <;> apply Fin.ext <;> norm_num [pattern] <;> omega
    · refine ⟨8,?_,?_,?_⟩ <;> apply Fin.ext <;> norm_num [pattern] <;> omega
  obtain ⟨r,hr0,hr1,hr2⟩ := hclass
    (p224_support_firstSquareType q t₁ t₂ 0)
    (p224_support_firstSquareType q t₁ t₂ 1)
    (p224_support_firstSquareType q t₁ t₂ 2) hfirst (by omega) (by omega)
  refine ⟨r,?_⟩
  funext s
  fin_cases s
  · exact hr0.symm
  · exact hr1.symm
  · exact hr2.symm

private theorem p224_support_projected_literal_zero_of_no_pattern
    (K : Type u) [Field K] (q : Nat)
    (sigma : Fin 3 -> Fin 5)
    (hunsupported : ∀ r : Fin 9, sigma ≠ pattern r)
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
      exact congrArg F (p224_support_fourLiteralTerms_eq_basis_tprod K q t₁ t₂ t₃ t₄)
    _ = 0 := by
      dsimp only [F]
      rw [PiTensorProduct.map_tprod]
      erw [PiTensorProduct.map_tprod]
      by_cases hcoarse : ∀ s,
          cwFourthPairGrade q
              (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s) =
            modeTotalGrade s
      · obtain ⟨r, hr⟩ := p224_support_fourLiteralTerms_outer_pattern
          q t₁ t₂ t₃ t₄ hcoarse
        have haddress :
            (fun s => p224_support_firstSquareType q t₁ t₂ s) ≠ sigma := by
          intro heq
          exact hunsupported r (heq.symm.trans hr)
        have hdiff : ∃ s,
            p224_support_firstSquareType q t₁ t₂ s ≠ sigma s := by
          by_contra hnone
          push Not at hnone
          exact haddress (funext hnone)
        obtain ⟨s, hs⟩ := hdiff
        apply (PiTensorProduct.tprod K).map_coord_zero s
        rw [p224_support_coarse_blockProj_fourth_basis, dif_pos (hcoarse s)]
        let pc : ModeIndex q s :=
          ⟨cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s, hcoarse s⟩
        change (outerGrading K q).blockProj s (sigma s)
          (canonicalBasis K q s pc) = 0
        rw [p224_support_outer_blockProj_basis, dif_neg]
        simpa [pc, outerGrade, p224_support_firstSquareType,
          cwFourthIndexOfLiteralTerms] using hs
      · push Not at hcoarse
        obtain ⟨s, hs⟩ := hcoarse
        apply (PiTensorProduct.tprod K).map_coord_zero s
        rw [p224_support_coarse_blockProj_fourth_basis, dif_neg hs]
        simp

private theorem p224_support_linearMap_pair_fintype_sum
    {R I M N P : Type*} [Semiring R] [Fintype I]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    (A : N →ₗ[R] P) (B : M →ₗ[R] N) (f : I → M) :
    A (B (∑ i, f i)) = ∑ i, A (B (f i)) := by
  rw [map_sum B, map_sum A]

private theorem p224_support_outer_block_zero_of_no_pattern
    (K : Type u) [Field K] (q : Nat)
    (sigma : Fin 3 -> Fin 5)
    (hunsupported : ∀ r : Fin 9, sigma ≠ pattern r) :
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
      exact p224_support_linearMap_pair_fintype_sum A B f₄
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
          exact p224_support_linearMap_pair_fintype_sum A B f₃
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
              exact p224_support_linearMap_pair_fintype_sum A B f₂
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
                  exact p224_support_linearMap_pair_fintype_sum A B f₁
                _ = 0 := by
                  apply Fintype.sum_eq_zero
                  intro t₁
                  dsimp only [A, B, f₁]
                  exact p224_support_projected_literal_zero_of_no_pattern
                    K q sigma hunsupported t₁ t₂ t₃ t₄

end MME.StothersFourth.Phi224

theorem phi224_outer_grading_support
    {K : Type u} [Field K] (q : Nat) (sigma : Fin 3 -> Fin 5)
    (h : (MME.StothersFourth.Phi224.outerGrading K q).blockTensor sigma ≠ 0) :
    ∃ r : Fin 9, sigma = MME.StothersFourth.Phi224.pattern r := by
  by_contra hnone
  push Not at hnone
  exact h (MME.StothersFourth.Phi224.p224_support_outer_block_zero_of_no_pattern
    K q sigma hnone)
end

section
open BigOperators

namespace MME.StothersFourth.Phi224

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

private theorem projectedFiberCard
    {N : ℕ} (w : ProfileWord N) (i : Fin 3) (s : Fin 5) :
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => modeWord w i j = s)).card =
      ∑ r : {r : Fin 9 // pattern r i = s},
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => w j = r.1)).card := by
  classical
  let e :
      {j : Fin (2 * N) // modeWord w i j = s} ≃
        Sigma fun r : {r : Fin 9 // pattern r i = s} =>
          {j : Fin (2 * N) // w j = r.1} := {
    toFun j := ⟨⟨w j.1, j.2⟩, ⟨j.1, rfl⟩⟩
    invFun x := ⟨x.2.1, by
      change pattern (w x.2.1) i = s
      rw [x.2.2]
      exact x.1.2⟩
    left_inv j := by
      apply Subtype.ext
      rfl
    right_inv x := by
      rcases x with ⟨⟨r, hr⟩, ⟨j, hj⟩⟩
      cases hj
      rfl
  }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Fintype.card_subtype]

private theorem sum_ite_eq_sum_subtype
    {beta iota M : Type*} [Fintype beta] [DecidableEq iota]
    [AddCommMonoid M] (q : beta → iota) (i : iota) (f : beta → M) :
    (∑ b : beta, if q b = i then f b else 0) =
      ∑ b : {b : beta // q b = i}, f b.1 := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    ((Finset.univ : Finset beta).filter (fun b => q b = i))
    (fun b => by simp) f

theorem sum_fin9 {M : Type*} [AddCommMonoid M] (f : Fin 9 → M) :
 (∑ r,f r)=f 0+(f 1+(f 2+(f 3+(f 4+(f 5+(f 6+(f 7+f 8))))))) := by
 simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
 rfl

theorem pattern_injective : Function.Injective pattern := by
 have h (r : Fin 9) : r.val=3*(pattern r 0).val+(pattern r 1).val := by fin_cases r <;> decide
 intro r s hrs
 apply Fin.ext
 rw [h r,h s,congrFun hrs 0,congrFun hrs 1]

def orbit (r : Fin 9) : Fin 5 := ⟨min r.val (8-r.val),by omega⟩
def orbitMultiplicity (a b c d : ℕ) (r : Fin 5) : ℕ :=
 match r.val with
 | 0 => 2*a
 | 1 => 2*b
 | 2 => 2*c
 | 3 => 2*b
 | _ => 2*d

theorem cell_counts (N alpha beta gamma delta : ℕ) (hsum : alpha+2*beta+gamma+delta=N)
 (i : Fin 3) (j : Fin 5) :
 (∑ r : Fin 9,if pattern r i=j then profileMultiplicity alpha beta gamma delta r else 0)=
 marginalMultiplicity N alpha beta gamma delta i j := by
 rw [sum_fin9]
 fin_cases i <;> fin_cases j
 · change alpha+(beta+(gamma+(0+(0+(0+(0+(0+(0))))))))=alpha+beta+gamma
   omega
 · change 0+(0+(0+(beta+(2*delta+(beta+(0+(0+(0))))))))=2*beta+2*delta
   omega
 · change 0+(0+(0+(0+(0+(0+(gamma+(beta+(alpha))))))))=alpha+beta+gamma
   omega
 · change 0+(0+(0+(0+(0+(0+(0+(0+(0))))))))=0
   omega
 · change 0+(0+(0+(0+(0+(0+(0+(0+(0))))))))=0
   omega
 · change alpha+(0+(0+(beta+(0+(0+(gamma+(0+(0))))))))=alpha+beta+gamma
   omega
 · change 0+(beta+(0+(0+(2*delta+(0+(0+(beta+(0))))))))=2*beta+2*delta
   omega
 · change 0+(0+(gamma+(0+(0+(beta+(0+(0+(alpha))))))))=alpha+beta+gamma
   omega
 · change 0+(0+(0+(0+(0+(0+(0+(0+(0))))))))=0
   omega
 · change 0+(0+(0+(0+(0+(0+(0+(0+(0))))))))=0
   omega
 · change 0+(0+(0+(0+(0+(0+(0+(0+(alpha))))))))=alpha
   omega
 · change 0+(0+(0+(0+(0+(beta+(0+(beta+(0))))))))=2*beta
   omega
 · change 0+(0+(gamma+(0+(2*delta+(0+(gamma+(0+(0))))))))=2*gamma+2*delta
   omega
 · change 0+(beta+(0+(beta+(0+(0+(0+(0+(0))))))))=2*beta
   omega
 · change alpha+(0+(0+(0+(0+(0+(0+(0+(0))))))))=alpha
   omega

theorem exact_to_marginal (N alpha beta gamma delta : ℕ) (hsum : alpha+2*beta+gamma+delta=N)
 (w : SymmetricProfileWord N alpha beta gamma delta) :
 ∀ i j,(Finset.univ.filter (fun n ↦ modeWord w.1 i n=j)).card=marginalMultiplicity N alpha beta gamma delta i j := by
 intro i j
 rw [projectedFiberCard,← sum_ite_eq_sum_subtype (fun r : Fin 9 ↦ pattern r i) j
   (fun r ↦ (Finset.univ.filter (fun n ↦ w.1 n=r)).card)]
 simp_rw [w.2]
 exact cell_counts N alpha beta gamma delta hsum i j

theorem marginal_orbit_counts {N alpha beta gamma delta : ℕ}
 (w : ExactProfileWord N alpha beta gamma delta) :
 ∀ r : Fin 5,(Finset.univ.filter (fun n ↦ orbit (w.1 n)=r)).card=orbitMultiplicity alpha beta gamma delta r := by
 classical
 let k : Fin 9 → ℕ := fun r ↦ (Finset.univ.filter (fun n ↦ w.1 n=r)).card
 have h24 := w.2 (2 : Fin 3) (4 : Fin 5)
 rw [projectedFiberCard,← sum_ite_eq_sum_subtype (fun r : Fin 9 ↦ pattern r 2) (4 : Fin 5) k,sum_fin9] at h24
 change k 0+(0+(0+(0+(0+(0+(0+(0+(0))))))))=alpha at h24
 have h20 := w.2 (2 : Fin 3) (0 : Fin 5)
 rw [projectedFiberCard,← sum_ite_eq_sum_subtype (fun r : Fin 9 ↦ pattern r 2) (0 : Fin 5) k,sum_fin9] at h20
 change 0+(0+(0+(0+(0+(0+(0+(0+(k 8))))))))=alpha at h20
 have h23 := w.2 (2 : Fin 3) (3 : Fin 5)
 rw [projectedFiberCard,← sum_ite_eq_sum_subtype (fun r : Fin 9 ↦ pattern r 2) (3 : Fin 5) k,sum_fin9] at h23
 change 0+(k 1+(0+(k 3+(0+(0+(0+(0+(0))))))))=2*beta at h23
 have h21 := w.2 (2 : Fin 3) (1 : Fin 5)
 rw [projectedFiberCard,← sum_ite_eq_sum_subtype (fun r : Fin 9 ↦ pattern r 2) (1 : Fin 5) k,sum_fin9] at h21
 change 0+(0+(0+(0+(0+(k 5+(0+(k 7+(0))))))))=2*beta at h21
 have h00 := w.2 (0 : Fin 3) (0 : Fin 5)
 rw [projectedFiberCard,← sum_ite_eq_sum_subtype (fun r : Fin 9 ↦ pattern r 0) (0 : Fin 5) k,sum_fin9] at h00
 change k 0+(k 1+(k 2+(0+(0+(0+(0+(0+(0))))))))=alpha+beta+gamma at h00
 have h01 := w.2 (0 : Fin 3) (1 : Fin 5)
 rw [projectedFiberCard,← sum_ite_eq_sum_subtype (fun r : Fin 9 ↦ pattern r 0) (1 : Fin 5) k,sum_fin9] at h01
 change 0+(0+(0+(k 3+(k 4+(k 5+(0+(0+(0))))))))=2*beta+2*delta at h01
 have h02 := w.2 (0 : Fin 3) (2 : Fin 5)
 rw [projectedFiberCard,← sum_ite_eq_sum_subtype (fun r : Fin 9 ↦ pattern r 0) (2 : Fin 5) k,sum_fin9] at h02
 change 0+(0+(0+(0+(0+(0+(k 6+(k 7+(k 8))))))))=alpha+beta+gamma at h02
 have h10 := w.2 (1 : Fin 3) (0 : Fin 5)
 rw [projectedFiberCard,← sum_ite_eq_sum_subtype (fun r : Fin 9 ↦ pattern r 1) (0 : Fin 5) k,sum_fin9] at h10
 change k 0+(0+(0+(k 3+(0+(0+(k 6+(0+(0))))))))=alpha+beta+gamma at h10
 have h11 := w.2 (1 : Fin 3) (1 : Fin 5)
 rw [projectedFiberCard,← sum_ite_eq_sum_subtype (fun r : Fin 9 ↦ pattern r 1) (1 : Fin 5) k,sum_fin9] at h11
 change 0+(k 1+(0+(0+(k 4+(0+(0+(k 7+(0))))))))=2*beta+2*delta at h11
 have h12 := w.2 (1 : Fin 3) (2 : Fin 5)
 rw [projectedFiberCard,← sum_ite_eq_sum_subtype (fun r : Fin 9 ↦ pattern r 1) (2 : Fin 5) k,sum_fin9] at h12
 change 0+(0+(k 2+(0+(0+(k 5+(0+(0+(k 8))))))))=alpha+beta+gamma at h12
 have h22 := w.2 (2 : Fin 3) (2 : Fin 5)
 rw [projectedFiberCard,← sum_ite_eq_sum_subtype (fun r : Fin 9 ↦ pattern r 2) (2 : Fin 5) k,sum_fin9] at h22
 change 0+(0+(k 2+(0+(k 4+(0+(k 6+(0+(0))))))))=2*gamma+2*delta at h22
 have hcount (r : Fin 5) : (Finset.univ.filter (fun n ↦ orbit (w.1 n)=r)).card=
   ∑ v : Fin 9,if orbit v=r then k v else 0 := by
   let e : {n : Fin (2*N) // orbit (w.1 n)=r} ≃ Sigma fun v : {v : Fin 9 // orbit v=r} ↦ {n : Fin (2*N) // w.1 n=v.1} := {
     toFun n := ⟨⟨w.1 n.1,n.2⟩,⟨n.1,rfl⟩⟩
     invFun x := ⟨x.2.1,by rw [x.2.2];exact x.1.2⟩
     left_inv n := by apply Subtype.ext;rfl
     right_inv x := by rcases x with ⟨⟨v,hv⟩,⟨n,hn⟩⟩;cases hn;rfl }
   rw [← Fintype.card_subtype,Fintype.card_congr e,Fintype.card_sigma,sum_ite_eq_sum_subtype]
   apply Finset.sum_congr rfl
   intro v hv
   rw [Fintype.card_subtype]
 intro r
 rw [hcount,sum_fin9]
 fin_cases r
 · change k 0+(0+(0+(0+(0+(0+(0+(0+(k 8))))))))=2*alpha
   omega
 · change 0+(k 1+(0+(0+(0+(0+(0+(k 7+(0))))))))=2*beta
   omega
 · change 0+(0+(k 2+(0+(0+(0+(k 6+(0+(0))))))))=2*gamma
   omega
 · change 0+(0+(0+(k 3+(0+(k 5+(0+(0+(0))))))))=2*beta
   omega
 · change 0+(0+(0+(0+(k 4+(0+(0+(0+(0))))))))=2*delta
   omega

end MME.StothersFourth.Phi224
end

section
open MME BigOperators MME.StothersFourth.Phi224
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace MME.StothersFourth.Phi224
 def reversePattern (r : Fin 9) : Fin 9 := ⟨8-r.val,by omega⟩
 noncomputable def squareObj (K : Type u) [Field K] (q : ℕ) : Fin 9 → TensorObj K 3 :=
 ![MMObj K 1 1 1,MMObj K 1 1 (2*q),MMObj K 1 1 (q^2+2),MMObj K (2*q) 1 1,
   coupledObj K q,TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q),
   MMObj K (q^2+2) 1 1,TensorObj.permObj cyclicPerm (coupledObj K q),MMObj K 1 (q^2+2) 1]
 noncomputable def fullComponentObj (K : Type u) [Field K] (q : ℕ) (r : Fin 9) : TensorObj K 3 :=
 TensorObj.kron (squareObj K q r) (squareObj K q (reversePattern r))
 noncomputable def componentObj (K : Type u) [Field K] (q : ℕ) (r : Fin 5) : TensorObj K 3 :=
 fullComponentObj K q ⟨r.val,by omega⟩
 noncomputable def fineSourceObj
     (K : Type u) [Field K] (q : ℕ) (r : Fin 9) : TensorObj K 3 :=
   (TensorObj.TypeGrading.kronGrading
      (cwSquareCanonicalGrading K q)
      (cwSquareCanonicalGrading K q)).blockSubtensor
     (fun s ↦ finProdFinEquiv (pattern r s, pattern (reversePattern r) s))
end MME.StothersFourth.Phi224
theorem phi224_kron_restrict
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

theorem phi224_kronFin_restrict
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
      exact phi224_kron_restrict hd (h 0)
        (ih (fun r ↦ X r.succ) (fun r ↦ Y r.succ)
          (fun r ↦ h r.succ))

theorem phi224_square_restrict {K : Type u} [Field K] (q : ℕ) (r : Fin 9) :
 TensorObj.Restrict (squareObj K q r) ((cwSquareCanonicalGrading K q).blockSubtensor (pattern r)) := by
 obtain ⟨_,h004,_,_,h013,_,h103,_,_,_,h022,h202,h220⟩ := mme_CW_square_canonical_elementary_blocks (K := K) q
 fin_cases r
 · have hp : pattern (0 : Fin 9)=cwSquareBlockType 0 0 4 := by funext s;fin_cases s <;> rfl
   change TensorObj.Restrict (squareObj K q (0 : Fin 9)) ((cwSquareCanonicalGrading K q).blockSubtensor (pattern (0 : Fin 9)))
   rw [hp]
   exact h004
 · have hp : pattern (1 : Fin 9)=cwSquareBlockType 0 1 3 := by funext s;fin_cases s <;> rfl
   change TensorObj.Restrict (squareObj K q (1 : Fin 9)) ((cwSquareCanonicalGrading K q).blockSubtensor (pattern (1 : Fin 9)))
   rw [hp]
   exact h013
 · have hp : pattern (2 : Fin 9)=cwSquareBlockType 0 2 2 := by funext s;fin_cases s <;> rfl
   change TensorObj.Restrict (squareObj K q (2 : Fin 9)) ((cwSquareCanonicalGrading K q).blockSubtensor (pattern (2 : Fin 9)))
   rw [hp]
   exact h022
 · have hp : pattern (3 : Fin 9)=cwSquareBlockType 1 0 3 := by funext s;fin_cases s <;> rfl
   change TensorObj.Restrict (squareObj K q (3 : Fin 9)) ((cwSquareCanonicalGrading K q).blockSubtensor (pattern (3 : Fin 9)))
   rw [hp]
   exact h103
 · have hp : pattern (4 : Fin 9)=cwSquareBlockType 1 1 2 := by funext s;fin_cases s <;> rfl
   change TensorObj.Restrict (squareObj K q (4 : Fin 9)) ((cwSquareCanonicalGrading K q).blockSubtensor (pattern (4 : Fin 9)))
   rw [hp]
   exact mme_CW_square_canonical_coupled112_restrict q
 · have hp : pattern (5 : Fin 9)=cwSquareBlockType 1 2 1 := by funext s;fin_cases s <;> rfl
   change TensorObj.Restrict (squareObj K q (5 : Fin 9)) ((cwSquareCanonicalGrading K q).blockSubtensor (pattern (5 : Fin 9)))
   rw [hp]
   exact mme_CW_square_canonical_coupled121_restrict q
 · have hp : pattern (6 : Fin 9)=cwSquareBlockType 2 0 2 := by funext s;fin_cases s <;> rfl
   change TensorObj.Restrict (squareObj K q (6 : Fin 9)) ((cwSquareCanonicalGrading K q).blockSubtensor (pattern (6 : Fin 9)))
   rw [hp]
   exact h202
 · have hp : pattern (7 : Fin 9)=cwSquareBlockType 2 1 1 := by funext s;fin_cases s <;> rfl
   change TensorObj.Restrict (squareObj K q (7 : Fin 9)) ((cwSquareCanonicalGrading K q).blockSubtensor (pattern (7 : Fin 9)))
   rw [hp]
   exact mme_CW_square_canonical_coupled211_restrict q
 · have hp : pattern (8 : Fin 9)=cwSquareBlockType 2 2 0 := by funext s;fin_cases s <;> rfl
   change TensorObj.Restrict (squareObj K q (8 : Fin 9)) ((cwSquareCanonicalGrading K q).blockSubtensor (pattern (8 : Fin 9)))
   rw [hp]
   exact h220
theorem phi224_fine_source_restrict {K : Type u} [Field K] (q : ℕ) (r : Fin 9) :
 TensorObj.Restrict (fineSourceObj K q r) ((outerGrading K q).blockSubtensor (pattern r)) := by
 apply phi224_fine_block_restrict_outer_block (K := K) q (pattern r) (pattern (reversePattern r))
 intro s
 fin_cases r <;> fin_cases s <;> rfl

theorem phi224_component_restrict {K : Type u} [Field K] (q : ℕ) (r : Fin 9) :
 TensorObj.Restrict (fullComponentObj K q r) (fineSourceObj K q r) := by
 exact (phi224_kron_restrict (by omega) (phi224_square_restrict q r)
   (phi224_square_restrict q (reversePattern r))).trans
   (mme_TypeGrading_kron_blockSubtensor_iso (cwSquareCanonicalGrading K q)
     (cwSquareCanonicalGrading K q) (pattern r) (pattern (reversePattern r))).1

theorem phi224_orbit_component_restrict {K : Type u} [Field K] (q : ℕ) (r : Fin 9) :
 TensorObj.Restrict (componentObj K q (orbit r)) (fullComponentObj K q r) := by
 have hcomm (X Y : TensorObj K 3) : TensorObj.Isomorphic (TensorObj.kron X Y) (TensorObj.kron Y X) :=
   TensorQ.toQ_eq_iff.mp (mul_comm (TensorQ.toQ X) (TensorQ.toQ Y))
 fin_cases r
 · exact TensorObj.Restrict.refl _
 · exact TensorObj.Restrict.refl _
 · exact TensorObj.Restrict.refl _
 · exact TensorObj.Restrict.refl _
 · exact TensorObj.Restrict.refl _
 · exact (hcomm (squareObj K q 3) (squareObj K q 5)).1
 · exact (hcomm (squareObj K q 2) (squareObj K q 6)).1
 · exact (hcomm (squareObj K q 1) (squareObj K q 7)).1
 · exact (hcomm (squareObj K q 0) (squareObj K q 8)).1

theorem phi224_exact_product_restrict {K : Type u} [Field K] (q : ℕ) {N a b c d : ℕ}
    (w : ExactProfileWord N a b c d) :
    TensorObj.Restrict
      (TensorObj.kronFin 5 (fun r ↦ (componentObj K q r).kronPow (orbitMultiplicity a b c d r)))
      (gradedAddressBlock (outerGrading K q) (modeWord w.1)) := by
  classical
  have hgroup := mme_kronFin_group_by_exact_fibers_iso (componentObj K q) (fun j ↦ orbit (w.1 j))
    (orbitMultiplicity a b c d) (by intro r; rw [Fintype.card_subtype]; exact marginal_orbit_counts w r)
  refine hgroup.2.trans (phi224_kronFin_restrict (d := 3) (by omega) (2*N) _ _ ?_)
  intro j
  exact ((phi224_orbit_component_restrict (K := K) q (w.1 j)).trans (phi224_component_restrict (K := K) q (w.1 j))).trans (phi224_fine_source_restrict (K := K) q (w.1 j))

def phi224_cyclic_address {N a b c d : ℕ} (e : CyclicExactEdge N a b c d) : Fin 3 → Fin (2*N) → Fin 125 :=
  fun i j ↦ mmeCyclicTripleGrade (fun s ↦ modeWord e.1.1 s j)
    (fun s ↦ modeWord e.2.1.1 s j) (fun s ↦ modeWord e.2.2.1 s j) i

theorem phi224_cyclic_product_restrict {K : Type u} [Field K] (q : ℕ) {N a b c d : ℕ}
    (e : CyclicExactEdge N a b c d) :
    TensorObj.Restrict
      (cyclicSymmetrization (TensorObj.kronFin 5
        (fun r ↦ (componentObj K q r).kronPow (orbitMultiplicity a b c d r))))
      (gradedAddressBlock (mmeCyclicTripleGrading (outerGrading K q)) (phi224_cyclic_address e)) := by
  have hA := phi224_exact_product_restrict (K := K) q e.1
  have hB := phi224_exact_product_restrict (K := K) q e.2.1
  have hC := phi224_exact_product_restrict (K := K) q e.2.2
  have hh := phi224_kron_restrict (K := K) (by omega) hA
    (phi224_kron_restrict (K := K) (by omega)
      (TensorObj.permObj_restrict cyclicPerm hB)
      (TensorObj.permObj_restrict (cyclicPerm.trans cyclicPerm) hC))
  rw [cyclicSymmetrization_eq_public_perm]
  exact hh.trans (mme_cyclic_grading_address_block_iso (outerGrading K q)
    (modeWord e.1.1) (modeWord e.2.1.1) (modeWord e.2.2.1)).1
end

section
open BigOperators
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- Equal histograms admit a coordinate permutation matching the words. -/
theorem histogram_permutation {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f g : A → B) (h : ∀ b,Fintype.card {a // f a=b}=Fintype.card {a // g a=b}) :
    ∃ e : A ≃ A, ∀ a,g (e a)=f a := by
  classical
  let es := fun b ↦ Fintype.equivOfCardEq (h b)
  exact ⟨Equiv.ofFiberEquiv es,Equiv.ofFiberEquiv_map es⟩

theorem histogram_reindex {A B : Type*} [Fintype A] (e : A ≃ A) (f : A → B) (b : B) :
    Nat.card {a // f (e a)=b}=Nat.card {a // f a=b} := by
  exact Nat.card_congr {
    toFun a := ⟨e a.1,a.2⟩
    invFun a := ⟨e.symm a.1,by simpa using a.2⟩
    left_inv a := by apply Subtype.ext;exact e.symm_apply_apply a.1
    right_inv a := by apply Subtype.ext;exact e.apply_symm_apply a.1 }

/-- A word family invariant under coordinate permutations has uniform projection fibers. -/
theorem invariant_histogram_fibers {A R B : Type*} [Fintype A] [Fintype R] [Fintype B] [DecidableEq B]
    (P : (A → R) → Prop) (q : R → B)
    (hP : ∀ e : A ≃ A,∀ w,P w → P (fun a ↦ w (e a)))
    (f g : A → B) (h : ∀ b,Fintype.card {a // f a=b}=Fintype.card {a // g a=b}) :
    Nat.card {w : {w : A → R // P w} // (fun a ↦ q (w.1 a))=f}=
      Nat.card {w : {w : A → R // P w} // (fun a ↦ q (w.1 a))=g} := by
  classical
  obtain ⟨e,he⟩ := histogram_permutation g f (fun b ↦ (h b).symm)
  let F := {w : {w : A → R // P w} // (fun a ↦ q (w.1 a))=f}
  let G := {w : {w : A → R // P w} // (fun a ↦ q (w.1 a))=g}
  let eqv : F ≃ G := {
    toFun w := ⟨⟨fun a ↦ w.1.1 (e a),hP e w.1.1 w.1.2⟩,by
      funext a
      exact (congrFun w.2 (e a)).trans (he a)⟩
    invFun w := ⟨⟨fun a ↦ w.1.1 (e.symm a),hP e.symm w.1.1 w.1.2⟩,by
      funext a
      exact (congrFun w.2 (e.symm a)).trans (by simpa using (he (e.symm a)).symm)⟩
    left_inv w := by apply Subtype.ext;apply Subtype.ext;funext a;exact congrArg w.1.1 (e.apply_symm_apply a)
    right_inv w := by apply Subtype.ext;apply Subtype.ext;funext a;exact congrArg w.1.1 (e.symm_apply_apply a) }
  exact Nat.card_congr eqv

/-- Constant fibers factor the cardinality of a finite map. -/
theorem uniform_fiber_card_factorization {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (D : ℕ) (h : ∀ y,Nat.card {x // f x=y}=D) :
    Nat.card X=Nat.card Y*D := by
  classical
  calc
    Nat.card X=Nat.card (Sigma fun y ↦ {x // f x=y}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ y,Nat.card {x // f x=y} := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]
    _ = Nat.card Y*D := by simp_rw [h];simp [Nat.card_eq_fintype_card]
end

section
open MME BigOperators MME.StothersFourth.Phi224
set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable local instance (N a b c d : ℕ) : Fintype (ExactProfileWord N a b c d) := exactProfileWordFintype N a b c d

theorem phi224_count_totals (N a b c d : ℕ) (hsum : a+2*b+c+d=N) :
 ∑ r : Fin 9,profileMultiplicity a b c d r=2*N := by
 simp [Fin.sum_univ_succ,profileMultiplicity]
 omega

theorem phi224_marginal_totals (N a b c d : ℕ) (hsum : a+2*b+c+d=N) (i : Fin 3) :
 ∑ s : Fin 5,marginalMultiplicity N a b c d i s=2*N := by
 fin_cases i <;> simp [Fin.sum_univ_succ,marginalMultiplicity] <;> omega

/-- A generic prescribed histogram family has its multinomial cardinality. -/
theorem phi224_histogram_card {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
 (k : B → ℕ) (hk : ∑ b,k b=Fintype.card A) :
 Nat.card {w : A → B // ∀ b,(Finset.univ.filter (fun a ↦ w a=b)).card=k b}=
 Nat.multinomial Finset.univ k := by
 classical
 let e : {w : A → B // ∀ b,(Finset.univ.filter (fun a ↦ w a=b)).card=k b} ≃
   {w : A → B // ∀ b,Fintype.card {a // w a=b}=k b} := {
   toFun w := ⟨w.1,by intro b;rw [Fintype.card_subtype];exact w.2 b⟩
   invFun w := ⟨w.1,by intro b;rw [← Fintype.card_subtype];exact w.2 b⟩
   left_inv w := by apply Subtype.ext;rfl
   right_inv w := by apply Subtype.ext;rfl }
 rw [Nat.card_congr e,Nat.card_eq_fintype_card,mme_fintype_prescribed_fiber_function_card k hk]
 simp only [Nat.multinomial,hk]

theorem phi224_exact_nonempty (N a b c d : ℕ) (hsum : a+2*b+c+d=N) :
 Nonempty (ExactProfileWord N a b c d) := by
 classical
 have hcard : Nat.card (SymmetricProfileWord N a b c d)=Nat.multinomial Finset.univ (profileMultiplicity a b c d) :=
   phi224_histogram_card (profileMultiplicity a b c d) (by simpa using phi224_count_totals N a b c d hsum)
 have hp : 0<Nat.card (SymmetricProfileWord N a b c d) := by
   rw [hcard];exact Nat.multinomial_pos _ _
 obtain ⟨w⟩ := (Nat.card_pos_iff.mp hp).1
 exact ⟨⟨w.1,exact_to_marginal N a b c d hsum w⟩⟩

noncomputable def phi224_mode_degree (N a b c d : ℕ) (i : Fin 3) : ℕ :=
 Nat.card (ExactProfileWord N a b c d)/Nat.multinomial Finset.univ (marginalMultiplicity N a b c d i)

theorem phi224_reindex_preserves (N a b c d : ℕ) (e : Fin (2*N) ≃ Fin (2*N))
 (w : ProfileWord N) (hw : ∀ i s,(Finset.univ.filter (fun j ↦ modeWord w i j=s)).card=marginalMultiplicity N a b c d i s) :
 ∀ i s,(Finset.univ.filter (fun j ↦ pattern (w (e j)) i=s)).card=marginalMultiplicity N a b c d i s := by
 intro i s
 have hh := histogram_reindex e (modeWord w i) s
 change (Finset.univ.filter (fun j ↦ modeWord w i (e j) = s)).card =
   marginalMultiplicity N a b c d i s
 simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,hw] using
   hh.trans (by
     simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hw i s)

theorem phi224_mode_fiber_and_factorization (N a b c d : ℕ) (hsum : a+2*b+c+d=N)
 (i : Fin 3) (x : ExactProfileWord N a b c d) :
 Nat.card {w : ExactProfileWord N a b c d // modeWord w.1 i=modeWord x.1 i}=phi224_mode_degree N a b c d i ∧
 Nat.card (ExactProfileWord N a b c d)=
   Nat.multinomial Finset.univ (marginalMultiplicity N a b c d i)*phi224_mode_degree N a b c d i := by
 classical
 let X := ExactProfileWord N a b c d
 let Y := {f : Fin (2*N) → Fin 5 // ∀ s,(Finset.univ.filter (fun j ↦ f j=s)).card=marginalMultiplicity N a b c d i s}
 letI : Fintype Y := Fintype.ofFinite Y
 let f : X → Y := fun w ↦ ⟨modeWord w.1 i,w.2 i⟩
 let D := Nat.card {w : X // modeWord w.1 i=modeWord x.1 i}
 have hY : Nat.card Y=Nat.multinomial Finset.univ (marginalMultiplicity N a b c d i) :=
   phi224_histogram_card _ (by simpa using phi224_marginal_totals N a b c d hsum i)
 have hfiber (y : Y) : Nat.card {w : X // f w=y}=D := by
   let e : {w : X // f w=y} ≃ {w : X // modeWord w.1 i=y.1} := {
     toFun w := ⟨w.1,congrArg Subtype.val w.2⟩
     invFun w := ⟨w.1,Subtype.ext w.2⟩
     left_inv w := by apply Subtype.ext;rfl
     right_inv w := by apply Subtype.ext;rfl }
   rw [Nat.card_congr e]
   exact invariant_histogram_fibers
     (fun w : ProfileWord N ↦ ∀ l s,(Finset.univ.filter (fun j ↦ modeWord w l j=s)).card=marginalMultiplicity N a b c d l s)
     (fun r ↦ pattern r i) (phi224_reindex_preserves N a b c d) y.1 (modeWord x.1 i)
     (by intro s;rw [Fintype.card_subtype,Fintype.card_subtype,y.2 s,x.2 i s])
 have hfactor := uniform_fiber_card_factorization f D hfiber
 rw [hY] at hfactor
 have hM : 0<Nat.multinomial Finset.univ (marginalMultiplicity N a b c d i) := Nat.multinomial_pos _ _
 have hD : phi224_mode_degree N a b c d i=D := by
   unfold phi224_mode_degree
   rw [hfactor,Nat.mul_div_cancel_left D hM]
 exact ⟨hD.symm,by simpa only [hD] using hfactor⟩

theorem mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
 (N a b c d : ℕ) (hsum : a+2*b+c+d=N) (x : ExactProfileWord N a b c d) (i : Fin 3) :
 Nat.card {w : ExactProfileWord N a b c d // modeWord w.1 i=modeWord x.1 i}=phi224_mode_degree N a b c d i :=
 (phi224_mode_fiber_and_factorization N a b c d hsum i x).1

theorem phi224_mode_factorization (N a b c d : ℕ) (hsum : a+2*b+c+d=N) (i : Fin 3) :
 Nat.card (ExactProfileWord N a b c d)=
   Nat.multinomial Finset.univ (marginalMultiplicity N a b c d i)*phi224_mode_degree N a b c d i := by
 obtain ⟨x⟩ := phi224_exact_nonempty N a b c d hsum
 exact (phi224_mode_fiber_and_factorization N a b c d hsum i x).2
end

section
open BigOperators

set_option autoImplicit false
set_option warningAsError true

private def tripleFiberEquiv
    {A B C D : Type*} (f : A → B) (g : A → C) (h : A → D)
    (x y z : A) :
    {p : A × (A × A) //
      (f p.1, (g p.2.1, h p.2.2)) = (f x, (g y, h z))} ≃
      {a : A // f a = f x} ×
        ({a : A // g a = g y} × {a : A // h a = h z}) where
  toFun p :=
    (⟨p.1.1, congrArg Prod.fst p.2⟩,
      (⟨p.1.2.1, congrArg (fun q ↦ q.2.1) p.2⟩,
        ⟨p.1.2.2, congrArg (fun q ↦ q.2.2) p.2⟩))
  invFun q :=
    ⟨(q.1.1, (q.2.1.1, q.2.2.1)), by
      apply Prod.ext
      · exact q.1.2
      · apply Prod.ext
        · exact q.2.1.2
        · exact q.2.2.2⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv q := by
    rcases q with ⟨q0, q1, q2⟩
    rfl

theorem mme_stothers_phi224_cyclic_mode_fiber_card
    (N alpha beta gamma delta : ℕ) (hsum : alpha + 2*beta + gamma + delta = N)
    (e : MME.StothersFourth.Phi224.CyclicExactEdge
      N alpha beta gamma delta)
    (i : Fin 3) :
    let D := phi224_mode_degree N alpha beta gamma delta
    Nat.card
        {f : MME.StothersFourth.Phi224.CyclicExactEdge
            N alpha beta gamma delta //
          MME.StothersFourth.Phi224.cyclicModeWord f i =
            MME.StothersFourth.Phi224.cyclicModeWord e i} =
      D 0 * (D 1 * D 2) := by
  dsimp only
  let A := MME.StothersFourth.Phi224.ExactProfileWord
    N alpha beta gamma delta
  fin_cases i
  · let equiv := tripleFiberEquiv
      (fun w : A ↦ MME.StothersFourth.Phi224.modeWord w.1 0)
      (fun w : A ↦ MME.StothersFourth.Phi224.modeWord w.1 2)
      (fun w : A ↦ MME.StothersFourth.Phi224.modeWord w.1 1)
      e.1 e.2.1 e.2.2
    change Nat.card
      {p : A × (A × A) //
        ((MME.StothersFourth.Phi224.modeWord p.1.1 0),
          ((MME.StothersFourth.Phi224.modeWord p.2.1.1 2),
            (MME.StothersFourth.Phi224.modeWord p.2.2.1 1))) =
        ((MME.StothersFourth.Phi224.modeWord e.1.1 0),
          ((MME.StothersFourth.Phi224.modeWord e.2.1.1 2),
            (MME.StothersFourth.Phi224.modeWord e.2.2.1 1)))} = _
    rw [Nat.card_congr equiv, Nat.card_prod, Nat.card_prod]
    rw [mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.1 0,
      mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.2.1 2,
      mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.2.2 1]
    ring
  · let equiv := tripleFiberEquiv
      (fun w : A ↦ MME.StothersFourth.Phi224.modeWord w.1 1)
      (fun w : A ↦ MME.StothersFourth.Phi224.modeWord w.1 0)
      (fun w : A ↦ MME.StothersFourth.Phi224.modeWord w.1 2)
      e.1 e.2.1 e.2.2
    change Nat.card
      {p : A × (A × A) //
        ((MME.StothersFourth.Phi224.modeWord p.1.1 1),
          ((MME.StothersFourth.Phi224.modeWord p.2.1.1 0),
            (MME.StothersFourth.Phi224.modeWord p.2.2.1 2))) =
        ((MME.StothersFourth.Phi224.modeWord e.1.1 1),
          ((MME.StothersFourth.Phi224.modeWord e.2.1.1 0),
            (MME.StothersFourth.Phi224.modeWord e.2.2.1 2)))} = _
    rw [Nat.card_congr equiv, Nat.card_prod, Nat.card_prod]
    rw [mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.1 1,
      mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.2.1 0,
      mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.2.2 2]
    ring
  · let equiv := tripleFiberEquiv
      (fun w : A ↦ MME.StothersFourth.Phi224.modeWord w.1 2)
      (fun w : A ↦ MME.StothersFourth.Phi224.modeWord w.1 1)
      (fun w : A ↦ MME.StothersFourth.Phi224.modeWord w.1 0)
      e.1 e.2.1 e.2.2
    change Nat.card
      {p : A × (A × A) //
        ((MME.StothersFourth.Phi224.modeWord p.1.1 2),
          ((MME.StothersFourth.Phi224.modeWord p.2.1.1 1),
            (MME.StothersFourth.Phi224.modeWord p.2.2.1 0))) =
        ((MME.StothersFourth.Phi224.modeWord e.1.1 2),
          ((MME.StothersFourth.Phi224.modeWord e.2.1.1 1),
            (MME.StothersFourth.Phi224.modeWord e.2.2.1 0)))} = _
    rw [Nat.card_congr equiv, Nat.card_prod, Nat.card_prod]
    rw [mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.1 2,
      mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.2.1 1,
      mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.2.2 0]
    ring
end

section
open BigOperators
open MME.StothersFourth.Phi224

set_option autoImplicit false
set_option warningAsError true

private theorem basic_doubled_hash_AP
    {R : Type} [CommRing R] {N alpha beta gamma delta : ℕ}
    (b : R) (w : Fin (2 * N) → R)
    (x y z : ExactProfileWord N alpha beta gamma delta)
    (hsupp : CoordinatewiseSupported x y z) :
    MME.StothersFourth.Phi233.doubledXHash (R := R) (N := N)
        b w (modeWord x.1 0) +
      MME.StothersFourth.Phi233.doubledYHash (R := R) (N := N)
        b w (modeWord y.1 1) =
      (2 : R) * MME.StothersFourth.Phi233.doubledZHash
        (R := R) (N := N) b w (modeWord z.1 2) := by
  have hsum (j : Fin (2 * N)) :
      (modeWord x.1 0 j).val + (modeWord y.1 1 j).val +
          (modeWord z.1 2 j).val = 4 := by
    obtain ⟨r, h0, h1, h2⟩ := hsupp j
    rw [← h0, ← h1, ← h2]
    fin_cases r <;> decide
  have hpoint (j : Fin (2 * N)) :
      ((2 * (modeWord x.1 0 j).val : ℕ) : R) * w j +
          ((2 * (modeWord y.1 1 j).val : ℕ) : R) * w j =
        2 * (((4 : R) - ((modeWord z.1 2 j).val : R)) * w j) := by
    have hr :
        ((modeWord x.1 0 j).val : R) +
            ((modeWord y.1 1 j).val : R) +
            ((modeWord z.1 2 j).val : R) = 4 := by
      have hr' := congrArg (fun n : ℕ ↦ (n : R)) (hsum j)
      push_cast at hr'
      exact hr'
    push_cast
    linear_combination 2 * w j * hr
  calc
    MME.StothersFourth.Phi233.doubledXHash (R := R) (N := N)
          b w (modeWord x.1 0) +
        MME.StothersFourth.Phi233.doubledYHash (R := R) (N := N)
          b w (modeWord y.1 1) =
        4 * b +
          ((∑ j, ((2 * (modeWord x.1 0 j).val : ℕ) : R) * w j) +
            ∑ j, ((2 * (modeWord y.1 1 j).val : ℕ) : R) * w j) := by
      simp only [MME.StothersFourth.Phi233.doubledXHash,
        MME.StothersFourth.Phi233.doubledYHash]
      ring
    _ = 4 * b + ∑ j,
          (((2 * (modeWord x.1 0 j).val : ℕ) : R) * w j +
            ((2 * (modeWord y.1 1 j).val : ℕ) : R) * w j) := by
      rw [Finset.sum_add_distrib]
    _ = 4 * b + ∑ j,
          2 * (((4 : R) - ((modeWord z.1 2 j).val : R)) * w j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      exact hpoint j
    _ = (2 : R) * MME.StothersFourth.Phi233.doubledZHash
          (R := R) (N := N) b w (modeWord z.1 2) := by
      rw [← Finset.mul_sum]
      simp only [MME.StothersFourth.Phi233.doubledZHash]
      ring

theorem mme_stothers_phi224_cyclic_affine_hash_AP
    {p N alpha beta gamma delta : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p)
    (x y z : CyclicExactEdge N alpha beta gamma delta)
    (hsupp : CyclicCoordinatewiseSupported x y z) :
    cyclicAffineHash p N alpha beta gamma delta w shift offset 0 x +
        cyclicAffineHash p N alpha beta gamma delta w shift offset 1 y =
      2 * cyclicAffineHash p N alpha beta gamma delta w shift offset 2 z := by
  have ha := basic_doubled_hash_AP
    (2 * offset) (w 0) x.1 y.1 z.1 hsupp.1
  have hb := basic_doubled_hash_AP
    0 (w 1) y.2.1 z.2.1 x.2.1 hsupp.2.1
  have hc := basic_doubled_hash_AP
    offset (w 2) z.2.2 x.2.2 y.2.2 hsupp.2.2
  dsimp only [cyclicAffineHash]
  linear_combination ha - 2 * hb - 2 * hc
end

section
open BigOperators
open MME.StothersFourth.Phi224

set_option autoImplicit false
set_option warningAsError true

theorem mme_stothers_phi224_cyclic_affine_hash_normal_form
    {p N alpha beta gamma delta : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e : CyclicExactEdge N alpha beta gamma delta) :
    cyclicAffineHash p N alpha beta gamma delta w shift offset i e =
      shift + (![0, 12 * offset, 6 * offset] : Fin 3 → ZMod p) i +
        ∑ r : Fin 3, ∑ j : Fin (2 * N),
          cyclicHashModeCode p N i (cyclicModeWord e i) r j * w r j := by
  have hsumMul (f : Fin (2 * N) → ZMod p) (c : ZMod p) :
      (∑ j, f j) * c = ∑ j, f j * c := by
    simpa using
      (Finset.sum_mul (Finset.univ : Finset (Fin (2 * N))) f c)
  have hscale2 (u : Fin (2 * N) → Fin 5)
      (v : Fin (2 * N) → ZMod p) :
      (∑ j, ((u j).val : ZMod p) * v j * 2) * 2 =
        ∑ j, ((u j).val : ZMod p) * v j * 4 := by
    calc
      _ = ∑ j, (((u j).val : ZMod p) * v j * 2) * 2 := hsumMul _ 2
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  have hscale4 (u : Fin (2 * N) → Fin 5)
      (v : Fin (2 * N) → ZMod p) :
      (∑ j, (-((u j).val : ZMod p) * v j + v j * 4)) * 4 =
        ∑ j, (-((u j).val : ZMod p) * v j * 4 + v j * 16) := by
    calc
      _ = ∑ j,
          (-((u j).val : ZMod p) * v j + v j * 4) * 4 := hsumMul _ 4
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  fin_cases i
  · simp [cyclicAffineHash, cyclicHashModeCode,
      MME.StothersFourth.Phi233.cyclicHashModeCode, cyclicModeWord,
      MME.StothersFourth.Phi233.doubledXHash,
      MME.StothersFourth.Phi233.doubledYHash,
      MME.StothersFourth.Phi233.doubledZHash, Fin.sum_univ_succ]
    ring_nf
    rw [hscale2 (modeWord e.2.2.1 1) (w 2)]
    have hb := hscale4 (modeWord e.2.1.1 2) (w 1)
    simp only [neg_mul] at hb
    rw [hb]
  · simp [cyclicAffineHash, cyclicHashModeCode,
      MME.StothersFourth.Phi233.cyclicHashModeCode, cyclicModeWord,
      MME.StothersFourth.Phi233.doubledXHash,
      MME.StothersFourth.Phi233.doubledYHash,
      MME.StothersFourth.Phi233.doubledZHash, Fin.sum_univ_succ]
    ring_nf
    rw [hscale2 (modeWord e.2.1.1 0) (w 1)]
    have hc := hscale4 (modeWord e.2.2.1 2) (w 2)
    simp only [neg_mul] at hc
    rw [hc]
  · simp [cyclicAffineHash, cyclicHashModeCode,
      MME.StothersFourth.Phi233.cyclicHashModeCode, cyclicModeWord,
      MME.StothersFourth.Phi233.doubledXHash,
      MME.StothersFourth.Phi233.doubledYHash,
      MME.StothersFourth.Phi233.doubledZHash, Fin.sum_univ_succ]
    ring
end

section
open MME.StothersFourth.Phi224

set_option autoImplicit false
set_option warningAsError true

private theorem exactProfile_eq_of_all_modes
    {N alpha beta gamma delta : ℕ} (hsum : alpha + 2*beta + gamma + delta = N)
    (x y : ExactProfileWord N alpha beta gamma delta)
    (h0 : modeWord x.1 0 = modeWord y.1 0)
    (h1 : modeWord x.1 1 = modeWord y.1 1)
    (h2 : modeWord x.1 2 = modeWord y.1 2) :
    x = y := by
  apply Subtype.ext
  funext j
  have hpattern := MME.StothersFourth.Phi224.pattern_injective
  apply hpattern
  funext i
  fin_cases i
  · exact congrFun h0 j
  · exact congrFun h1 j
  · exact congrFun h2 j

theorem mme_stothers_phi224_cyclic_mode_word_tuple_injective
    (N alpha beta gamma delta : ℕ) (hsum : alpha + 2*beta + gamma + delta = N) :
    Function.Injective
      (fun e : MME.StothersFourth.Phi224.CyclicExactEdge
          N alpha beta gamma delta ↦
        MME.StothersFourth.Phi224.cyclicModeWord e) := by
  intro e f hef
  have hv0 := congrFun hef (0 : Fin 3)
  have hv1 := congrFun hef (1 : Fin 3)
  have hv2 := congrFun hef (2 : Fin 3)
  have he0 : e.1 = f.1 := exactProfile_eq_of_all_modes hsum e.1 f.1
    (congrArg Prod.fst hv0)
    (congrArg Prod.fst hv1)
    (congrArg Prod.fst hv2)
  have he1 : e.2.1 = f.2.1 := exactProfile_eq_of_all_modes hsum e.2.1 f.2.1
    (congrArg (fun q ↦ q.2.1) hv1)
    (congrArg (fun q ↦ q.2.1) hv2)
    (congrArg (fun q ↦ q.2.1) hv0)
  have he2 : e.2.2 = f.2.2 := exactProfile_eq_of_all_modes hsum e.2.2 f.2.2
    (congrArg (fun q ↦ q.2.2) hv2)
    (congrArg (fun q ↦ q.2.2) hv0)
    (congrArg (fun q ↦ q.2.2) hv1)
  exact Prod.ext he0 (Prod.ext he1 he2)
end

section
open BigOperators
open MME.StothersFourth.Phi224

set_option autoImplicit false
set_option warningAsError true

theorem phi224_hash_difference
    {p N alpha beta gamma delta : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e f : CyclicExactEdge N alpha beta gamma delta) :
    cyclicAffineHash p N alpha beta gamma delta w shift offset i e -
        cyclicAffineHash p N alpha beta gamma delta w shift offset i f =
      ∑ r : Fin 3, ∑ j : Fin (2 * N),
        (cyclicHashModeCode p N i (cyclicModeWord e i) r j -
          cyclicHashModeCode p N i (cyclicModeWord f i) r j) * w r j := by
  rw [mme_stothers_phi224_cyclic_affine_hash_normal_form w shift offset i e,
    mme_stothers_phi224_cyclic_affine_hash_normal_form w shift offset i f]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  ring

open BigOperators
open MME.StothersFourth.Phi224

set_option autoImplicit false
set_option warningAsError true

theorem phi224_hash_edge
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e : CyclicExactEdge N alpha beta gamma delta)
    (S : Finset (ZMod p)) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : (I → ZMod p) × ZMod p) (i : Fin 3) ↦
      cyclicAffineHash p N alpha beta gamma delta
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
    cyclicAffineHash p N alpha beta gamma delta
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
      (mme_stothers_phi224_cyclic_affine_hash_normal_form
        (p := p) (N := N) (alpha := alpha) (beta := beta)
        (gamma := gamma) (delta := delta) 
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) 0 e)
  have hH2 (q : (I → ZMod p) × ZMod p) :
      H q 2 = shift q.1 + q.2 + L2 q.1 := by
    rw [show H q 2 =
        shift q.1 + 6 * ((6 : ZMod p)⁻¹ * q.2) + L2 q.1 by
      simpa [H, weights, shift, L2] using
        (mme_stothers_phi224_cyclic_affine_hash_normal_form
          (p := p) (N := N) (alpha := alpha) (beta := beta)
          (gamma := gamma) (delta := delta) 
          (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) 2 e)]
    rw [← mul_assoc, mul_inv_cancel₀ h6, one_mul]
  have hAP (q : (I → ZMod p) × ZMod p) :
      H q 0 + H q 1 = 2 * H q 2 := by
    have hsupp : CyclicCoordinatewiseSupported e e e := by
      refine ⟨?_, ?_, ?_⟩
      · intro j; exact ⟨e.1.1 j,rfl,rfl,rfl⟩
      · intro j; exact ⟨e.2.1.1 j,rfl,rfl,rfl⟩
      · intro j; exact ⟨e.2.2.1 j,rfl,rfl,rfl⟩
    exact mme_stothers_phi224_cyclic_affine_hash_AP
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
open MME.StothersFourth.Phi224

set_option autoImplicit false
set_option warningAsError true

theorem phi224_hash_pair
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hsum : alpha+2*beta+gamma+delta=N)
    (e f : CyclicExactEdge N alpha beta gamma delta)
    (S : Finset (ZMod p)) (hne : e ≠ f) (shared : Fin 3)
    (hshared : cyclicModeWord e shared = cyclicModeWord f shared) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : (I → ZMod p) × ZMod p)
        (i : Fin 3) (a : CyclicExactEdge N alpha beta gamma delta) ↦
      cyclicAffineHash p N alpha beta gamma delta
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i a
    let retain := fun (q : (I → ZMod p) × ZMod p)
        (a : CyclicExactEdge N alpha beta gamma delta) ↦
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
      (i : Fin 3) (a : CyclicExactEdge N alpha beta gamma delta) ↦
    cyclicAffineHash p N alpha beta gamma delta
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i a
  let retain := fun (q : (I → ZMod p) × ZMod p)
      (a : CyclicExactEdge N alpha beta gamma delta) ↦
    ∃ s ∈ S, ∀ i : Fin 3, H q i a = s
  let joint : ((I → ZMod p) × ZMod p) → Prop := fun q ↦
    retain q e ∧ retain q f
  change ((Finset.univ.filter joint).card) ≤ _
  have hcard : Fintype.card I = 6 * N + 1 := by
    simp [I]
    omega
  have hmodeNe : cyclicModeWord e ≠ cyclicModeWord f := by
    intro h
    exact hne (mme_stothers_phi224_cyclic_mode_word_tuple_injective N alpha beta gamma delta hsum h)
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
      (mme_stothers_phi224_cyclic_affine_hash_normal_form
        (p := p) (N := N) (alpha := alpha) (beta := beta)
        (gamma := gamma) (delta := delta) 
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) 0 e)
  have hH2 (q : (I → ZMod p) × ZMod p) :
      H q 2 e = shift q.1 + q.2 + L2 q.1 := by
    rw [show H q 2 e =
        shift q.1 + 6 * ((6 : ZMod p)⁻¹ * q.2) + L2 q.1 by
      simpa [H, weights, shift, L2] using
        (mme_stothers_phi224_cyclic_affine_hash_normal_form
          (p := p) (N := N) (alpha := alpha) (beta := beta)
          (gamma := gamma) (delta := delta) 
          (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) 2 e)]
    rw [← mul_assoc, mul_inv_cancel₀ h6, one_mul]
  have hvertex (q : (I → ZMod p) × ZMod p)
      (a b : CyclicExactEdge N alpha beta gamma delta) (i : Fin 3)
      (hab : cyclicModeWord a i = cyclicModeWord b i) :
      H q i a = H q i b := by
    dsimp only [H]
    rw [mme_stothers_phi224_cyclic_affine_hash_normal_form
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i a]
    rw [mme_stothers_phi224_cyclic_affine_hash_normal_form
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
      rw [← phi224_hash_difference
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
open MME BigOperators MME.StothersFourth.Phi224
set_option autoImplicit false
theorem phi224_supported_completion {N a b c d : ℕ} (hsum : a+2*b+c+d=N)
    (x y z : ExactProfileWord N a b c d) (hs : CoordinatewiseSupported x y z) :
    ∃ w : ExactProfileWord N a b c d,
      modeWord w.1 0=modeWord x.1 0 ∧ modeWord w.1 1=modeWord y.1 1 ∧ modeWord w.1 2=modeWord z.1 2 := by
  classical
  choose w hw using hs
  have hm (i : Fin 3) : modeWord w i = modeWord ((![x,y,z] : Fin 3 → ExactProfileWord N a b c d) i).1 i := by
    funext j
    fin_cases i
    · exact (hw j).1
    · exact (hw j).2.1
    · exact (hw j).2.2
  have hcounts : ∀ i s,(Finset.univ.filter (fun j ↦ modeWord w i j=s)).card=marginalMultiplicity N a b c d i s := by
    intro i s
    rw [hm i]
    exact ((![x,y,z] : Fin 3 → ExactProfileWord N a b c d) i).2 i s
  exact ⟨⟨w,hcounts⟩,hm 0,hm 1,hm 2⟩

theorem phi224_cyclic_completion {N a b c d : ℕ} (hsum : a+2*b+c+d=N)
    (x y z : CyclicExactEdge N a b c d) (hs : CyclicCoordinatewiseSupported x y z) :
    ∃ e : CyclicExactEdge N a b c d, cyclicModeWord e 0=cyclicModeWord x 0 ∧
      cyclicModeWord e 1=cyclicModeWord y 1 ∧ cyclicModeWord e 2=cyclicModeWord z 2 := by
  obtain ⟨u,hu0,hu1,hu2⟩ := phi224_supported_completion hsum x.1 y.1 z.1 hs.1
  obtain ⟨v,hv0,hv1,hv2⟩ := phi224_supported_completion hsum y.2.1 z.2.1 x.2.1 hs.2.1
  obtain ⟨w,hw0,hw1,hw2⟩ := phi224_supported_completion hsum z.2.2 x.2.2 y.2.2 hs.2.2
  exact ⟨(u,(v,w)),by simp only [cyclicModeWord,hu0,hv2,hw1]; rfl,
    by simp only [cyclicModeWord,hu1,hv0,hw2]; rfl,
    by simp only [cyclicModeWord,hu2,hv1,hw0]; rfl⟩
end

section
open MME BigOperators
open MME.StothersFourth.Phi224
set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable local instance p224FiniteExact (N a b c d : ℕ) : Fintype (ExactProfileWord N a b c d) :=
  exactProfileWordFintype N a b c d
noncomputable local instance p224FiniteEdge (N a b c d : ℕ) : Fintype (CyclicExactEdge N a b c d) :=
  cyclicExactEdgeFintype N a b c d

noncomputable def phi224_degree (N a b c d : ℕ) : ℕ :=
  phi224_mode_degree N a b c d 0*(phi224_mode_degree N a b c d 1*phi224_mode_degree N a b c d 2)

theorem phi224_hash_agrees_on_mode (p N a b c d : ℕ)
    (w : Fin 3 → Fin (2*N) → ZMod p) (shift offset : ZMod p)
    (i : Fin 3) (e f : CyclicExactEdge N a b c d)
    (h : cyclicModeWord e i=cyclicModeWord f i) :
    cyclicAffineHash p N a b c d w shift offset i e=cyclicAffineHash p N a b c d w shift offset i f := by
  rw [mme_stothers_phi224_cyclic_affine_hash_normal_form,
    mme_stothers_phi224_cyclic_affine_hash_normal_form,h]

theorem phi224_finite_hash_selection
    (N alpha beta gamma delta p : ℕ) (hN : 0 < N) (hsum : alpha + 2*beta + gamma + delta = N)
    [Fact p.Prime] (hp : 7 ≤ p) (S : Finset (ZMod p))
    (hfree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x+y=2*z → x=z ∧ z=y)
    (hlarge : 6 * ((phi224_degree N alpha beta gamma delta : ℕ) : ℝ) ≤ S.card) :
    ∃ kept : Finset (CyclicExactEdge N alpha beta gamma delta),
      ((∀ i : Fin 3, Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
        ∀ x y z : kept, CyclicCoordinatewiseSupported x.1 y.1 z.1 → x=y ∧ y=z) ∧
      (Fintype.card (CyclicExactEdge N alpha beta gamma delta) : ℝ) *
        ((S.card : ℝ) / (2 * (p : ℝ)^2)) ≤ kept.card := by
  classical
  let I := (Fin 3 × Fin (2*N)) ⊕ Unit
  let State := (I → ZMod p) × ZMod p
  let weights := fun w : I → ZMod p ↦ fun r j ↦ w (Sum.inl (r,j))
  let H := fun q : State ↦ cyclicAffineHash p N alpha beta gamma delta
    (weights q.1) (q.1 (Sum.inr ())) ((6 : ZMod p)⁻¹ * q.2)
  let retain := fun (q : State) (e : CyclicExactEdge N alpha beta gamma delta) ↦
    ∃ s ∈ S, ∀ i : Fin 3, H q i e = s
  let all : Finset (CyclicExactEdge N alpha beta gamma delta) := Finset.univ
  let D := phi224_degree N alpha beta gamma delta
  let ell : ℝ := (S.card : ℝ) / (2 * (p : ℝ)^2)
  have hp0 : 0 < p := by omega
  letI : NeZero p := ⟨by omega⟩
  have hstate : Fintype.card State = p^2 * p^(6*N) := by
    simp only [State, I, Fintype.card_prod, Fintype.card_fun, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_unit, ZMod.card]
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  have hdegree (i : Fin 3) (a : CyclicExactEdge N alpha beta gamma delta) (_ : a ∈ all) :
      (all.filter (fun b ↦ cyclicModeWord b i = cyclicModeWord a i)).card ≤ D := by
    have hh := mme_stothers_phi224_cyclic_mode_fiber_card N alpha beta gamma delta hsum a i
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,all,D,phi224_degree,phi224_mode_degree] using hh.le

  have hedge (a : CyclicExactEdge N alpha beta gamma delta) (_ : a ∈ all) :
      (Finset.univ.filter (fun q : State ↦ retain q a)).card = S.card * p^(6*N) :=
    phi224_hash_edge hp a S
  have hpair (ab : CyclicExactEdge N alpha beta gamma delta × CyclicExactEdge N alpha beta gamma delta)
      (hab : ab ∈ ((all ×ˢ all).filter (fun ab ↦ ab.1 ≠ ab.2 ∧
        ∃ i : Fin 3, cyclicModeWord ab.1 i = cyclicModeWord ab.2 i))) :
      (Finset.univ.filter (fun q : State ↦ retain q ab.1 ∧ retain q ab.2)).card ≤ p^(6*N) := by
    obtain ⟨_, hne, i, hi⟩ := Finset.mem_filter.mp hab
    exact phi224_hash_pair hp hsum ab.1 ab.2 S hne i hi
  have hclosure (q : State)
      (x : CyclicExactEdge N alpha beta gamma delta) (hx : x ∈ all.filter (retain q))
      (y : CyclicExactEdge N alpha beta gamma delta) (hy : y ∈ all.filter (retain q))
      (z : CyclicExactEdge N alpha beta gamma delta) (hz : z ∈ all.filter (retain q))
      (hs : CyclicCoordinatewiseSupported x y z) :
      ∃ e ∈ all.filter (retain q), cyclicModeWord e 0 = cyclicModeWord x 0 ∧
        cyclicModeWord e 1 = cyclicModeWord y 1 ∧
        cyclicModeWord e 2 = cyclicModeWord z 2 := by
    obtain ⟨sx, hsx, hx'⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨sy, hsy, hy'⟩ := (Finset.mem_filter.mp hy).2
    obtain ⟨sz, hsz, hz'⟩ := (Finset.mem_filter.mp hz).2
    have hap := mme_stothers_phi224_cyclic_affine_hash_AP (weights q.1) (q.1 (Sum.inr ())) ((6 : ZMod p)⁻¹*q.2) x y z hs
    change H q 0 x + H q 1 y = 2 * H q 2 z at hap
    rw [hx', hy', hz'] at hap
    obtain ⟨hxs, hsy'⟩ := hfree sx hsx sy hsy sz hsz hap
    obtain ⟨e, he0, he1, he2⟩ := phi224_cyclic_completion hsum x y z hs
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he0, he1, he2⟩
    refine ⟨sz, hsz, ?_⟩
    intro i
    fin_cases i
    · exact (phi224_hash_agrees_on_mode _ _ _ _ _ _ _ _ _ _ _ _ he0).trans ((hx' 0).trans hxs)
    · exact (phi224_hash_agrees_on_mode _ _ _ _ _ _ _ _ _ _ _ _ he1).trans ((hy' 1).trans hsy'.symm)
    · exact (phi224_hash_agrees_on_mode _ _ _ _ _ _ _ _ _ _ _ _ he2).trans (hz' 2)
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
open MME BigOperators MME.StothersFourth.Phi224
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable local instance p224BoundsExact (N a b c d : ℕ) : Fintype (ExactProfileWord N a b c d) := exactProfileWordFintype N a b c d
noncomputable local instance p224BoundsEdge (N a b c d : ℕ) : Fintype (CyclicExactEdge N a b c d) := cyclicExactEdgeFintype N a b c d

theorem phi224_degree_bounds (N a b c d : ℕ) (hsum : a+2*b+c+d=N) :
    1≤phi224_degree N a b c d ∧ phi224_degree N a b c d≤5^(12*N) := by
  classical
  obtain ⟨w⟩ := phi224_exact_nonempty N a b c d hsum
  let e : CyclicExactEdge N a b c d := (w,w,w)
  let F := {f : CyclicExactEdge N a b c d // cyclicModeWord f 0=cyclicModeWord e 0}
  have heq : Nat.card F=phi224_degree N a b c d :=
    mme_stothers_phi224_cyclic_mode_fiber_card N a b c d hsum e 0
  have hpos : 0<Nat.card F := (Nat.card_pos_iff).mpr ⟨⟨⟨e,rfl⟩⟩,inferInstance⟩
  have hle : Nat.card F≤Nat.card (CyclicExactEdge N a b c d) := by
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hw : Nat.card (ExactProfileWord N a b c d)≤9^(2*N) := by
    calc
      _ ≤ Nat.card (ProfileWord N) := by
        rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
        exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = _ := by simp [ProfileWord,Nat.card_eq_fintype_card]
  have hc : Nat.card (CyclicExactEdge N a b c d)=(Nat.card (ExactProfileWord N a b c d))^3 := by
    simp [CyclicExactEdge,Nat.card_prod,pow_succ];ring
  refine ⟨by omega,?_⟩
  rw [← heq]
  calc
    _ ≤ Nat.card (CyclicExactEdge N a b c d) := hle
    _ ≤ (9^(2*N))^3 := by rw [hc]; exact Nat.pow_le_pow_left hw 3
    _ = 9^(6*N) := by rw [← pow_mul];congr 1;omega
    _ ≤ 25^(6*N) := Nat.pow_le_pow_left (by omega) _
    _ = 5^(12*N) := by rw [show (25 : ℕ)=5^2 by norm_num,← pow_mul];congr 1;omega

theorem phi224_prime_parameters (N a b c d : ℕ) (hsum : a+2*b+c+d=N) :
    ∃ p : ℕ, Nat.Prime p ∧ 7≤p ∧ ∃ S : Finset (ZMod p),
      (∀ x∈S,∀ y∈S,∀ z∈S,x+y=2*z → x=z ∧ z=y) ∧
      6*(phi224_degree N a b c d : ℝ)≤S.card ∧
      (p : ℝ)≤(phi224_degree N a b c d : ℝ)*Real.exp (2000*Real.sqrt ((12*N+1 : ℕ) : ℝ)) := by
  classical
  let D := phi224_degree N a b c d
  obtain ⟨hD1,hD5⟩ := phi224_degree_bounds N a b c d hsum
  obtain ⟨p,hp,hp5,S,hSr,hSf,hSbig,hpbound⟩ :=
    mme_prime_behrend_dominates_bounded_collision_degree (12*N) D hD1 hD5
  have hcard := Finset.card_le_card hSr
  rw [Finset.card_range] at hcard
  have hScard : 6*D≤S.card := by exact_mod_cast hSbig
  have hp7 : 7≤p := by omega
  obtain ⟨hcastcard,hcastfree⟩ := mme_stothers_phi233_lower_half_cast_label_package p S hSr hSf
  exact ⟨p,hp,hp7,S.image (fun s : ℕ ↦ (s : ZMod p)),hcastfree,
    by simpa only [hcastcard] using hSbig,hpbound⟩

theorem phi224_capacity_identity (N a b c d : ℕ) (hsum : a+2*b+c+d=N) :
    (∏ i : Fin 3, Nat.multinomial Finset.univ (marginalMultiplicity N a b c d i))*
      phi224_degree N a b c d = (Nat.card (ExactProfileWord N a b c d))^3 := by
  have h0 := phi224_mode_factorization N a b c d hsum 0
  have h1 := phi224_mode_factorization N a b c d hsum 1
  have h2 := phi224_mode_factorization N a b c d hsum 2
  rw [Fin.prod_univ_three]
  unfold phi224_degree
  calc
    _ = (Nat.multinomial Finset.univ (marginalMultiplicity N a b c d 0)*phi224_mode_degree N a b c d 0)*
      (Nat.multinomial Finset.univ (marginalMultiplicity N a b c d 1)*phi224_mode_degree N a b c d 1)*
      (Nat.multinomial Finset.univ (marginalMultiplicity N a b c d 2)*phi224_mode_degree N a b c d 2) := by ring
    _ = _ := by rw [← h0,← h1,← h2];ring
end

section
open MME Real BigOperators Filter MME.StothersFourth.Phi224
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

noncomputable def phi224_entropy (a b c d : ℝ) : ℝ :=
 4*Real.negMulLog ((a+b+c)/2)+2*Real.negMulLog (b+d)+
 2*Real.negMulLog (a/2)+2*Real.negMulLog b+Real.negMulLog (c+d)

theorem phi224_multinomial_entropy (w : Fin 5 → ℕ) (n : ℕ) (hn : 0<n) (hsum : ∑ i,w i=n) :
    Real.exp ((n : ℝ)*∑ i,Real.negMulLog ((w i : ℝ)/n))≤
      (6*((n+1 : ℕ) : ℝ))^5*(Nat.multinomial Finset.univ w : ℝ) := by
  have h := mme_dwz_multinomial_entropy_polynomial_lower w 1 (by omega) (show 0<∑ i,w i by omega)
  have hlog : Real.log 2≠0 := (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne'
  simp only [hsum,Nat.mul_one,mul_one,one_mul,mme_modern_entropyBits,Fintype.card_fin] at h
  have he (x : ℝ) : (n : ℝ)*Real.log 2*(x/Real.log 2)=n*x := by field_simp
  rw [he] at h
  simpa only [Nat.cast_one,one_mul] using h

theorem phi224_capacity_entropy (N a b c d : ℕ) (hN : 0<N) (hsum : a+2*b+c+d=N) :
    Real.exp ((2*N : ℝ)*phi224_entropy (a/N) (b/N) (c/N) (d/N))≤
      (6*((2*N+1 : ℕ) : ℝ))^15*
      ((Nat.card (ExactProfileWord N a b c d) : ℝ)^3/(phi224_degree N a b c d : ℝ)) := by
  have hh (i : Fin 3) := phi224_multinomial_entropy (marginalMultiplicity N a b c d i)
    (2*N) (by omega) (phi224_marginal_totals N a b c d hsum i)
  have hprod := Finset.prod_le_prod (fun i (_ : i∈(Finset.univ : Finset (Fin 3))) ↦ (Real.exp_pos _).le)
    (fun i (_ : i∈(Finset.univ : Finset (Fin 3))) ↦ hh i)
  rw [← Real.exp_sum] at hprod
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hprod
  have hD : (phi224_degree N a b c d : ℝ)≠0 := by
    have hh := (phi224_degree_bounds N a b c d hsum).1
    exact_mod_cast (show phi224_degree N a b c d≠0 by omega)
  have hid := congrArg (fun x : ℕ ↦ (x : ℝ)) (phi224_capacity_identity N a b c d hsum)
  push_cast at hid
  have hratio : (∏ i : Fin 3,(Nat.multinomial Finset.univ (marginalMultiplicity N a b c d i) : ℝ))=
      (Nat.card (ExactProfileWord N a b c d) : ℝ)^3/(phi224_degree N a b c d : ℝ) :=
    (eq_div_iff hD).mpr hid
  rw [hratio] at hprod
  have hn0 : (N : ℝ)≠0 := by positivity
  have hsumE : (∑ i : Fin 3,(2*N : ℝ)*∑ s : Fin 5,
      Real.negMulLog ((marginalMultiplicity N a b c d i s : ℝ)/(2*N)))=
      (2*N : ℝ)*phi224_entropy (a/N) (b/N) (c/N) (d/N) := by
    simp only [Fin.sum_univ_succ]
    norm_num [Fin.succ,marginalMultiplicity]
    have habc : ((a : ℝ)+b+c)/(2*N)=((a/N)+(b/N)+(c/N))/2 := by ring
    have hbd : (2*(b : ℝ)+2*d)/(2*N)=(b/N)+(d/N) := by ring
    have ha : (a : ℝ)/(2*N)=(a/N)/2 := by ring
    have hb : (2*b : ℝ)/(2*N)=b/N := by ring
    have hcd : (2*(c : ℝ)+2*d)/(2*N)=(c/N)+(d/N) := by ring
    rw [habc,hbd,ha,hb,hcd]
    unfold phi224_entropy
    ring
  push_cast at hprod
  rw [hsumE] at hprod
  simpa only [← pow_mul,Nat.reduceMul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hprod
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
open MME Real BigOperators Filter MME.StothersFourth.Phi224
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem phi224_profile_surplus (L E H a b c d V : ℝ)
    (hL : 0<L) (hE : 0<E) (hH : 0<H) (ha : 0<a) (hb : 0<b) (hc : 0≤c)
    (hd : 0≤d) (hsumR : a+2*b+c+d=1) (hV : 0<V)
    (hVlt : Real.log V < phi224_entropy a b c d+(a+2*c)*Real.log H+
      (2*b)*Real.log E+(2*b+2*d)*Real.log L) :
    ∃ N alpha beta gamma delta : ℕ, 0<N ∧ alpha+2*beta+gamma+delta=N ∧
      V^(2*N)*(phi224_degree N alpha beta gamma delta : ℝ)*Real.exp (4000*Real.sqrt ((12*N+1 : ℕ) : ℝ)) <
      (Nat.card (ExactProfileWord N alpha beta gamma delta) : ℝ)^3*
        (H^(2*alpha+4*gamma)*E^(4*beta)*L^(4*beta+4*delta)) := by
  let A := fun n : ℕ ↦ Nat.floor (a*(n : ℝ))
  let B := fun n : ℕ ↦ Nat.floor (b*(n : ℝ))
  let C := fun n : ℕ ↦ Nat.floor (c*(n : ℝ))
  let D := fun n : ℕ ↦ n-(A n+2*B n+C n)
  have hABCn (n : ℕ) : A n+2*B n+C n≤n := by
    have hfa := Nat.floor_le (show 0≤a*(n : ℝ) by positivity)
    have hfb := Nat.floor_le (show 0≤b*(n : ℝ) by positivity)
    have hfc := Nat.floor_le (show 0≤c*(n : ℝ) by positivity)
    have hh : (A n : ℝ)+2*(B n : ℝ)+(C n : ℝ)≤n := by
      dsimp [A,B,C]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact_mod_cast hh
  have hsum (n : ℕ) : A n+2*B n+C n+D n=n := Nat.add_sub_of_le (hABCn n)
  have hA : Tendsto (fun n : ℕ ↦ (A n : ℝ)/(n : ℝ)) atTop (nhds a) :=
    (tendsto_nat_floor_mul_div_atTop ha.le).comp tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun n : ℕ ↦ (B n : ℝ)/(n : ℝ)) atTop (nhds b) :=
    (tendsto_nat_floor_mul_div_atTop hb.le).comp tendsto_natCast_atTop_atTop
  have hC : Tendsto (fun n : ℕ ↦ (C n : ℝ)/(n : ℝ)) atTop (nhds c) :=
    (tendsto_nat_floor_mul_div_atTop hc).comp tendsto_natCast_atTop_atTop
  have hD : Tendsto (fun n : ℕ ↦ (D n : ℝ)/(n : ℝ)) atTop (nhds d) := by
    have hh := (((tendsto_const_nhds (x := (1 : ℝ))).sub hA).sub (hB.const_mul 2)).sub hC
    rw [show 1-a-2*b-c=d by linarith] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ)≠0 := by positivity
    dsimp [D]
    rw [Nat.cast_sub (hABCn n),Nat.cast_add,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
    <;> ring
  let rate := fun n ↦ phi224_entropy (A n/n) (B n/n) (C n/n) (D n/n)+
    ((A n/n)+2*(C n/n))*Real.log H+(2*(B n/n))*Real.log E+(2*(B n/n)+2*(D n/n))*Real.log L
  have hneg {f : ℕ → ℝ} {x : ℝ} (h : Tendsto f atTop (nhds x)) :
      Tendsto (fun n ↦ Real.negMulLog (f n)) atTop (nhds (Real.negMulLog x)) :=
    Real.continuous_negMulLog.continuousAt.tendsto.comp h
  have hent : Tendsto (fun n ↦ phi224_entropy (A n/n) (B n/n) (C n/n) (D n/n)) atTop
      (nhds (phi224_entropy a b c d)) :=
    ((((((hneg (((hA.add hB).add hC).div_const 2)).const_mul 4).add ((hneg (hB.add hD)).const_mul 2)).add ((hneg (hA.div_const 2)).const_mul 2)).add ((hneg hB).const_mul 2)).add (hneg (hC.add hD)))
  have hrate := ((hent.add ((hA.add (hC.const_mul 2)).mul_const (Real.log H))).add
    ((hB.const_mul 2).mul_const (Real.log E))).add
    (((hB.const_mul 2).add (hD.const_mul 2)).mul_const (Real.log L))
  have hlim := hrate.sub phi125_penalty_limit
  have hevent := hlim.eventually (eventually_gt_nhds (by simpa only [sub_zero] using hVlt))
  obtain ⟨N,hN,hgap⟩ := ((eventually_gt_atTop 0).and hevent).exists
  let alpha := A N
  let beta := B N
  let gamma := C N
  let delta := D N
  let P : ℝ := 6*((2*N+1 : ℕ) : ℝ)
  let Q : ℝ := ((12*N+1 : ℕ) : ℝ)
  let D : ℝ := (phi224_degree N alpha beta gamma delta : ℝ)
  let T : ℝ := (Nat.card (ExactProfileWord N alpha beta gamma delta) : ℝ)^3
  let J := H^(2*alpha+4*gamma)*E^(4*beta)*L^(4*beta+4*delta)
  have hD : 0<D := by
    have hh := (phi224_degree_bounds N alpha beta gamma delta (hsum N)).1
    dsimp [D]
    exact_mod_cast (show 0<phi224_degree N alpha beta gamma delta by omega)
  have hP : 0<P := by dsimp [P]; positivity
  have hJ : 0<J := by dsimp [J]; positivity
  have hf := mul_le_mul_of_nonneg_right (phi224_capacity_entropy N alpha beta gamma delta hN (hsum N)) hJ.le
  have hlogJ : Real.log J=(2*N : ℝ)*
      (((alpha/N)+2*(gamma/N))*Real.log H+(2*(beta/N))*Real.log E+(2*(beta/N)+2*(delta/N))*Real.log L) := by
    dsimp [J]
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
      Real.log_pow,Real.log_pow,Real.log_pow]
    push_cast
    have hn0 : (N : ℝ)≠0 := by positivity
    field_simp
    <;> ring
  have hleft : Real.exp ((2*N : ℝ)*phi224_entropy (alpha/N) (beta/N) (gamma/N) (delta/N))*J=
      Real.exp ((2*N : ℝ)*rate N) := by
    rw [← Real.exp_log hJ,← Real.exp_add,hlogJ]
    congr 1
    dsimp [rate,alpha,beta,gamma,delta]
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
  refine ⟨N,alpha,beta,gamma,delta,hN,hsum N,?_⟩
  change V^(2*N)*D*Real.exp (4000*Real.sqrt Q)<T*J
  field_simp at hc'
  nlinarith only [hc']
end

section
open MME BigOperators MME.StothersFourth.Phi224
set_option autoImplicit false
set_option maxHeartbeats 200000
theorem phi224_cyclic_mixed_supported
    {K : Type u} [Field K] {N alpha beta gamma delta : ℕ}
    (x y z : CyclicExactEdge N alpha beta gamma delta)
    (hnz : ∀ j, (mmeCyclicTripleGrading (outerGrading K 6)).blockTensor
      (fun i ↦ phi224_cyclic_address (![x,y,z] i) i j) ≠ 0) :
    CyclicCoordinatewiseSupported x y z := by
  have hh (j : Fin (2*N)) :
      (fun i ↦ phi224_cyclic_address (![x,y,z] i) i j) =
      mmeCyclicTripleGrade
        (fun s ↦ modeWord ((![x.1,y.1,z.1] : Fin 3 → ExactProfileWord N alpha beta gamma delta) s).1 s j)
        (fun s ↦ modeWord ((![y.2.1,z.2.1,x.2.1] : Fin 3 → ExactProfileWord N alpha beta gamma delta) s).1 s j)
        (fun s ↦ modeWord ((![z.2.2,x.2.2,y.2.2] : Fin 3 → ExactProfileWord N alpha beta gamma delta) s).1 s j) := by
    funext i
    fin_cases i <;> rfl
  have hparts (j : Fin (2*N)) := mme_cyclic_triple_grading_nonzero_factors
    (outerGrading K 6) _ _ _ (by rw [← hh j]; exact hnz j)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    obtain ⟨r,hr⟩ := phi224_outer_grading_support 6 _ (hparts j).1
    exact ⟨r,congrFun hr.symm 0,congrFun hr.symm 1,congrFun hr.symm 2⟩
  · intro j
    obtain ⟨r,hr⟩ := phi224_outer_grading_support 6 _ (hparts j).2.1
    exact ⟨r,congrFun hr.symm 0,congrFun hr.symm 1,congrFun hr.symm 2⟩
  · intro j
    obtain ⟨r,hr⟩ := phi224_outer_grading_support 6 _ (hparts j).2.2
    exact ⟨r,congrFun hr.symm 0,congrFun hr.symm 1,congrFun hr.symm 2⟩

theorem phi224_induced_profile_restrict
    {K : Type u} [Field K] {N alpha beta gamma delta : ℕ} (hsum : alpha+2*beta+gamma+delta=N)
    (kept : Finset (CyclicExactEdge N alpha beta gamma delta))
    (hdiag : ∀ x y z : kept, CyclicCoordinatewiseSupported x.1 y.1 z.1 → x=y ∧ y=z) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin kept.card ↦
        cyclicSymmetrization (TensorObj.kronFin 5 (fun r ↦
          (componentObj K 6 r).kronPow (orbitMultiplicity alpha beta gamma delta r)))))
      ((cyclicSymmetrization (MME.StothersFourth.cwFourthConstituent K 6 2 2 4)).kronPow (2*N)) := by
  classical
  let A := fun j : Fin kept.card ↦ phi224_cyclic_address (kept.equivFin.symm j).1
  have hind (js : Fin 3 → Fin kept.card)
      (hnz : ∀ r, (mmeCyclicTripleGrading (outerGrading K 6)).blockTensor
        (fun i ↦ A (js i) i r) ≠ 0) : ∃ j, js = fun _ ↦ j := by
    let es := fun i ↦ kept.equivFin.symm (js i)
    have hs := phi224_cyclic_mixed_supported (K := K) (es 0).1 (es 1).1 (es 2).1 (by
      intro j
      have he : (![(es 0).1, (es 1).1, (es 2).1] : Fin 3 → CyclicExactEdge N alpha beta gamma delta) =
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
  exact phi224_cyclic_product_restrict 6 (kept.equivFin.symm j).1
end

section
open MME BigOperators Filter MME.StothersFourth.Phi224
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem phi224_value_downward {K : Type u} [Field K]
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

noncomputable def phi224_square_endpoint (tau : ℝ) : Fin 9 → ℝ :=
 ![1,MME.StothersFourth.E 6 tau,MME.StothersFourth.H 6 tau,MME.StothersFourth.E 6 tau,
 MME.StothersFourth.L 6 tau,MME.StothersFourth.L 6 tau,MME.StothersFourth.H 6 tau,
 MME.StothersFourth.L 6 tau,MME.StothersFourth.H 6 tau]

theorem phi224_square_endpoint_pos (tau : ℝ) (r : Fin 9) : 0<phi224_square_endpoint tau r := by
 fin_cases r <;> simp [phi224_square_endpoint,MME.StothersFourth.E,MME.StothersFourth.H,MME.StothersFourth.L] <;> positivity

theorem phi224_square_value {K : Type u} [Field K] (tau : ℝ) (htau : 2≤3*tau)
 (r : Fin 9) (V : ℝ) (hV : 0≤V) (hVB : V<phi224_square_endpoint tau r) :
 HasTauValueAtLeast (cyclicSymmetrization (squareObj K 6 r)) tau V := by
 have hMM (a b c : ℕ) (T : ℝ)
   (heq : ((((a*b*c)*(a*b*c)*(a*b*c) : ℕ) : ℝ)^tau)=T)
   (hVT : V<T) : HasTauValueAtLeast (cyclicSymmetrization (MMObj K a b c)) tau V :=
   phi224_value_downward _ _ _ _ (heq ▸ mme_MMObj_cyclic_tau_value a b c tau) hV hVT.le
 have hE : (((1728 : ℕ) : ℝ)^tau)=MME.StothersFourth.E 6 tau := by
   norm_num [MME.StothersFourth.E]
   rw [show (1728 : ℝ)=12^3 by norm_num,← Real.rpow_natCast_mul (by norm_num : (0 : ℝ)≤12) 3 tau]
   norm_num
 have hH : (((54872 : ℕ) : ℝ)^tau)=MME.StothersFourth.H 6 tau := by
   norm_num [MME.StothersFourth.H]
   rw [show (54872 : ℝ)=38^3 by norm_num,← Real.rpow_natCast_mul (by norm_num : (0 : ℝ)≤38) 3 tau]
   norm_num
 have hCoupled (W : ℝ) (hW : 0≤W) (hWL : W<MME.StothersFourth.L 6 tau) :
   HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau W :=
   mme_CW_q6_coupled_raw_cyclic_value_below tau htau W hW hWL
 fin_cases r
 · exact hMM 1 1 1 1 (by norm_num) hVB
 · exact hMM 1 1 12 _ hE hVB
 · exact hMM 1 1 38 _ hH hVB
 · exact hMM 12 1 1 _ hE hVB
 · exact hCoupled V hV hVB
 · exact mme_HasTauValueAtLeast_mono_restrict
     (mme_cyclicSymmetrization_isomorphic_cyclic_orbit (coupledObj K 6)).2.2 (hCoupled V hV hVB)
 · exact hMM 38 1 1 _ hH hVB
 · exact mme_HasTauValueAtLeast_mono_restrict
     (mme_cyclicSymmetrization_isomorphic_cyclic_orbit (coupledObj K 6)).1.2 (hCoupled V hV hVB)
 · exact hMM 1 38 1 _ hH hVB

noncomputable def phi224_endpoint (tau : ℝ) (r : Fin 5) : ℝ :=
 phi224_square_endpoint tau (⟨r.val,by omega⟩ : Fin 9) * phi224_square_endpoint tau (reversePattern (⟨r.val,by omega⟩ : Fin 9))

theorem phi224_endpoint_pos (tau : ℝ) (r : Fin 5) : 0<phi224_endpoint tau r :=
 mul_pos (phi224_square_endpoint_pos tau (⟨r.val,by omega⟩ : Fin 9)) (phi224_square_endpoint_pos tau (reversePattern (⟨r.val,by omega⟩ : Fin 9)))

theorem phi224_component_value {K : Type u} [Field K] (tau : ℝ) (htau : 2≤3*tau)
 (r : Fin 5) (V : ℝ) (hV : 0≤V) (hVB : V<phi224_endpoint tau r) :
 HasTauValueAtLeast (cyclicSymmetrization (componentObj K 6 r)) tau V := by
 exact mme_cyclic_kron_two_strict_below_product _ _ tau _ _
   (phi224_square_endpoint_pos tau (⟨r.val,by omega⟩ : Fin 9)) (phi224_square_endpoint_pos tau (reversePattern (⟨r.val,by omega⟩ : Fin 9)))
   (phi224_square_value tau htau (⟨r.val,by omega⟩ : Fin 9)) (phi224_square_value tau htau (reversePattern (⟨r.val,by omega⟩ : Fin 9))) V hV hVB

theorem phi224_profile_value {K : Type u} [Field K] (tau : ℝ) (htau : 2≤3*tau)
    (a b c d : ℕ) (W : ℝ) (hW : 0≤W)
    (hWB : W < MME.StothersFourth.H 6 tau^(2*a+4*c)*
      MME.StothersFourth.E 6 tau^(4*b)*MME.StothersFourth.L 6 tau^(4*b+4*d)) :
    HasTauValueAtLeast (cyclicSymmetrization (TensorObj.kronFin 5 (fun r ↦
      (componentObj K 6 r).kronPow (orbitMultiplicity a b c d r)))) tau W := by
  apply mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
    (componentObj K 6) (orbitMultiplicity a b c d) tau (phi224_endpoint tau)
    (phi224_endpoint_pos tau) (phi224_component_value tau htau) W hW
  convert hWB using 1
  simp [Fin.prod_univ_succ,Fin.succ,phi224_endpoint,phi224_square_endpoint,reversePattern,orbitMultiplicity,mul_pow,pow_add,pow_mul]
  ring
end

section
open MME
set_option autoImplicit false
set_option maxHeartbeats 300000

/-- Feasible weighted four-part profile for Davie--Stothers Lemma 5.1(iv). -/
theorem phi224_optimizer_profile
    (tau : ℝ) (hlo : 2 ≤ 3 * tau) (hhi : 3 * tau ≤ 3) :
    let E := MME.StothersFourth.E 6 tau
    let H := MME.StothersFourth.H 6 tau
    let L := MME.StothersFourth.L 6 tau
    let Z := 2 + 2 * E + H
    let a := 2 / Z
    let b := E / Z
    let sigma := 2 * H / (2 * H + L)
    let c := sigma - a - b
    let d := 1 - sigma - b
    0 < a ∧ 0 < b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      a + 2 * b + c + d = 1 ∧ a + b + c = sigma := by
  dsimp only
  let E := MME.StothersFourth.E 6 tau
  let H := MME.StothersFourth.H 6 tau
  let L := MME.StothersFourth.L 6 tau
  let Z := 2 + 2 * E + H
  let sigma := 2 * H / (2 * H + L)
  change 0 < 2 / Z ∧ 0 < E / Z ∧
    0 ≤ sigma - 2 / Z - E / Z ∧ 0 ≤ 1 - sigma - E / Z ∧
    2 / Z + 2 * (E / Z) + (sigma - 2 / Z - E / Z) +
      (1 - sigma - E / Z) = 1 ∧
    2 / Z + E / Z + (sigma - 2 / Z - E / Z) = sigma
  have hE : 0 < E := by unfold E MME.StothersFourth.E; positivity
  have hH : 0 < H := by unfold H MME.StothersFourth.H; positivity
  have hL : 0 < L := by unfold L MME.StothersFourth.L; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hHL : 0 < 2 * H + L := by positivity
  obtain ⟨_, _, _, _, hleft, hright⟩ :=
    mme_stothers_q6_EHL_optimizer_regime tau hlo hhi
  change (2 + E) * L ≤ 2 * H * (E + H) at hleft
  change 2 * E * H ≤ L * (2 + E + H) at hright
  have hc : 0 ≤ sigma - 2 / Z - E / Z := by
    have h : (2 + E) / Z ≤ 2 * H / (2 * H + L) := by
      apply (div_le_div_iff₀ hZ hHL).mpr
      dsimp [Z]
      nlinarith only [hleft]
    dsimp [sigma]
    rw [add_div] at h
    linarith
  have hd : 0 ≤ 1 - sigma - E / Z := by
    have h : E / Z ≤ L / (2 * H + L) := by
      apply (div_le_div_iff₀ hZ hHL).mpr
      dsimp [Z]
      nlinarith only [hright]
    have heq : 1 - sigma = L / (2 * H + L) := by
      dsimp [sigma]
      field_simp
      ring
    rw [heq]
    exact sub_nonneg.mpr h
  exact ⟨by positivity, by positivity, hc, hd, by ring, by ring⟩
end

section
open Real
set_option autoImplicit false
set_option maxHeartbeats 400000

/-- The optimized φ224 marginal entropy and component weights give its Table 1 rate. -/
theorem phi224_optimized_entropy_rate (E H L : ℝ) (hE : 0<E) (hH : 0<H) (hL : 0<L) :
    let Z := 2+2*E+H
    let u := 2*H/(2*H+L)
    let v := L/(2*H+L)
    let a := 2/Z
    let b := E/Z
    let t := H/Z
    4*Real.negMulLog (u/2)+2*Real.negMulLog v+2*Real.negMulLog (a/2)+
      2*Real.negMulLog b+Real.negMulLog t+
      (2*b)*Real.log E+(2*u-a-2*b)*Real.log H+(2*v)*Real.log L =
      Real.log ((2*H+L)^2*Z/H) := by
  dsimp only
  have hZ : 0<2+2*E+H := by positivity
  have hHL : 0<2*H+L := by positivity
  have h2 : (2 : ℝ)≠0 := by norm_num
  rw [Real.log_div (by positivity) hH.ne',Real.log_mul (by positivity) hZ.ne',Real.log_pow]
  simp only [Real.negMulLog]
  rw [Real.log_div (by positivity) h2,Real.log_div (by positivity) hHL.ne',Real.log_mul h2 hH.ne',
    Real.log_div hL.ne' hHL.ne',Real.log_div (by positivity) h2,Real.log_div h2 hZ.ne',
    Real.log_div hE.ne' hZ.ne',Real.log_div hH.ne' hZ.ne']
  norm_num only [Nat.cast_ofNat]
  field_simp
  <;> ring
end

section
open MME BigOperators Filter MME.StothersFourth.Phi224
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
theorem phi224_value_retention_bound
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

theorem phi224_value_at_profile
    {K : Type u} [Field K] (tau a b c d : ℝ)
    (htauLower : 2≤3*tau) (htauUpper : 3*tau≤3)
    (ha : 0<a) (hb : 0<b) (hc : 0≤c) (hd : 0≤d) (hsumR : a+2*b+c+d=1)
    (V : ℝ) (hV : 0≤V)
    (hVlt : V<Real.exp (phi224_entropy a b c d+(a+2*c)*Real.log (MME.StothersFourth.H 6 tau)+
      (2*b)*Real.log (MME.StothersFourth.E 6 tau)+(2*b+2*d)*Real.log (MME.StothersFourth.L 6 tau))) :
    HasTauValueAtLeast (cyclicSymmetrization (MME.StothersFourth.cwFourthConstituent K 6 2 2 4)) tau V := by
  classical
  let L := MME.StothersFourth.L 6 tau
  let E := MME.StothersFourth.E 6 tau
  let H := MME.StothersFourth.H 6 tau
  let Z := Real.exp (phi224_entropy a b c d+(a+2*c)*Real.log H+(2*b)*Real.log E+(2*b+2*d)*Real.log L)
  let U := (V+Z)/2
  have hVU : V<U := by dsimp [U,Z,L,E,H];linarith
  have hU : 0<U := lt_of_le_of_lt hV hVU
  have hUZ : U<Z := by dsimp [U,Z,L,E,H];linarith
  have hL : 0<L := by unfold L MME.StothersFourth.L;positivity
  have hE : 0<E := by unfold E MME.StothersFourth.E;positivity
  have hH : 0<H := by unfold H MME.StothersFourth.H;positivity
  obtain ⟨N,alpha,beta,gamma,delta,hN,hsum,hsurplus⟩ :=
    phi224_profile_surplus L E H a b c d U hL hE hH ha hb hc hd hsumR hU
      (by have hh := Real.log_lt_log hU hUZ; simpa only [Z,Real.log_exp] using hh)
  let D : ℝ := (phi224_degree N alpha beta gamma delta : ℝ)
  let F := Real.exp (2000*Real.sqrt ((12*N+1 : ℕ) : ℝ))
  let C : ℝ := (Nat.card (ExactProfileWord N alpha beta gamma delta) : ℝ)^3
  let B := H^(2*alpha+4*gamma)*E^(4*beta)*L^(4*beta+4*delta)
  have hD : 0<D := by
    have hh := (phi224_degree_bounds N alpha beta gamma delta hsum).1
    dsimp [D]
    exact_mod_cast (show 0<phi224_degree N alpha beta gamma delta by omega)
  have hF : 0<F := Real.exp_pos _
  have hB : 0<B := by dsimp [B];positivity
  obtain ⟨p,hp,hp7,S,hfree,hlarge,hpbound⟩ := phi224_prime_parameters N alpha beta gamma delta hsum
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨kept,⟨hmode,hdiag⟩,hcount⟩ := phi224_finite_hash_selection N alpha beta gamma delta p hN hsum hp7 S hfree hlarge
  letI : Fintype (ExactProfileWord N alpha beta gamma delta) := exactProfileWordFintype N alpha beta gamma delta
  letI : Fintype (CyclicExactEdge N alpha beta gamma delta) := cyclicExactEdgeFintype N alpha beta gamma delta
  have hcard : (Fintype.card (CyclicExactEdge N alpha beta gamma delta) : ℝ)=C := by
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
    phi224_value_retention_bound (p : ℝ) D F S.card C kept.card B (V^(2*N))
      (by exact_mod_cast hp.pos) hD hF (by dsimp [C];positivity) (by positivity) hB.le
      hpbound hlarge hcount hstrict
  have hv := mme_HasTauValueAtLeast_bigAdd_uniform_strict
    (fun _ : Fin kept.card ↦ cyclicSymmetrization (TensorObj.kronFin 5 (fun r ↦
      (componentObj K 6 r).kronPow (orbitMultiplicity alpha beta gamma delta r))))
    tau B hB.le (fun _ W hW hWB ↦ phi224_profile_value tau htauLower alpha beta gamma delta W hW hWB)
    (V^(2*N)) (pow_nonneg hV _) hVB
  have hpv := mme_HasTauValueAtLeast_mono_restrict
    (phi224_induced_profile_restrict (K := K) hsum kept hdiag) hv
  exact mme_HasTauValueAtLeast_kronPow_root _ tau V (2*N) (by omega) hV hpv

theorem phi224_value_below {K : Type u} [Field K] (tau : ℝ)
    (hlo : 2≤3*tau) (hhi : 3*tau≤3) (V : ℝ) (hV : 0≤V)
    (hVlt : V<MME.StothersFourth.classValue 6 tau 8) :
    HasTauValueAtLeast (cyclicSymmetrization (MME.StothersFourth.cwFourthConstituent K 6 2 2 4)) tau V := by
  let E := MME.StothersFourth.E 6 tau
  let H := MME.StothersFourth.H 6 tau
  let L := MME.StothersFourth.L 6 tau
  let Z := 2+2*E+H
  let a := 2/Z
  let b := E/Z
  let sigma := 2*H/(2*H+L)
  let c := sigma-a-b
  let d := 1-sigma-b
  have hE : 0<E := by unfold E MME.StothersFourth.E;positivity
  have hH : 0<H := by unfold H MME.StothersFourth.H;positivity
  have hL : 0<L := by unfold L MME.StothersFourth.L;positivity
  have hZ : 0<Z := by dsimp [Z];positivity
  have hHL : 0<2*H+L := by positivity
  obtain ⟨ha,hb,hc,hd,hsum,_⟩ := phi224_optimizer_profile tau hlo hhi
  change 0<a at ha
  change 0<b at hb
  change 0≤c at hc
  change 0≤d at hd
  change a+2*b+c+d=1 at hsum
  have habc : a+b+c=2*H/(2*H+L) := by dsimp [a,b,c,sigma];ring
  have hbd : b+d=L/(2*H+L) := by dsimp [b,d,sigma];field_simp;ring
  have hcd : c+d=H/Z := by dsimp [c,d,sigma,a,b,Z];field_simp;ring
  have hweightH : a+2*c=2*(2*H/(2*H+L))-a-2*b := by dsimp [c,sigma];ring
  have hrate : phi224_entropy a b c d+(a+2*c)*Real.log H+(2*b)*Real.log E+(2*b+2*d)*Real.log L=
      Real.log ((2*H+L)^2*Z/H) := by
    rw [show 2*b+2*d=2*(b+d) by ring,hweightH]
    unfold phi224_entropy
    rw [habc,hbd,hcd]
    have hh := phi224_optimized_entropy_rate E H L hE hH hL
    dsimp only at hh
    dsimp only [a,b,Z]
    convert hh using 1 <;> ring
  apply phi224_value_at_profile tau a b c d hlo hhi ha hb hc hd hsum V hV
  change V<Real.exp (phi224_entropy a b c d+(a+2*c)*Real.log H+(2*b)*Real.log E+(2*b+2*d)*Real.log L)
  rw [hrate,Real.exp_log (by positivity)]
  exact hVlt

theorem solution
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 8 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 2 2 4)) tau V := by
  intro V hV hVlt
  exact phi224_value_below (K := K) tau htauLower htauUpper V hV hVlt
end
