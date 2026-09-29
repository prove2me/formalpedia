-- Prove2me | solution 1 for mme_stothers_phi134_cyclic_value
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T21:10:31.746466+00:00
-- url     : https://prove2.me/submissions/03774a2d-7e66-4dc7-89b1-f11ec59dfd46

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_CW_fourth_literal_support_words
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_cyclic_triple_grading
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi116_fine_blocks
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash
import Definitions.Def_mme_tau_value
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_tensor_quotient
import Mathlib
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Tactic
import Theorems.Thm_mme_CW_fourth_tensor_eq_sum_literal_terms
import Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_HasTauValueAtLeast_bigAdd_uniform_strict
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
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
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso
import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree
import Theorems.Thm_mme_stothers_phi125_distinct_mode_code_difference_has_nonzero_coefficient
import Theorems.Thm_mme_stothers_phi134_fine_component_restrictions
import Theorems.Thm_mme_stothers_phi134_square_support_pair_classification
import Theorems.Thm_mme_stothers_phi233_lower_half_cast_label_package
import Theorems.Thm_mme_stothers_q6_EHL_optimizer_regime
import Theorems.Thm_mme_stothers_remaining_four_optimizer_certificates
import Theorems.Thm_mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers

/- Provenance: current-environment direct closure of the accepted
phi134 finite-certificate chain. It breaks the old mutual dependency
through `mme_stothers_lemma51_remaining_four_values` by inlining the
finite profile construction and deriving the cyclic value directly. -/

universe u

set_option warningAsError true
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/- Inlined legacy definition module: Def_mme_stothers_phi134_profile_data. -/
open MME BigOperators

namespace MME.StothersFourth.Phi134

set_option autoImplicit false

def ProfileAddress (N : ℕ) : Type := Fin 3 → Fin (2 * N) → Fin 5

def pattern : Fin 8 → Fin 3 → Fin 5 := ![cwSquareBlockType 0 0 4, cwSquareBlockType 0 1 3, cwSquareBlockType 0 2 2, cwSquareBlockType 0 3 1, cwSquareBlockType 1 0 3, cwSquareBlockType 1 1 2, cwSquareBlockType 1 2 1, cwSquareBlockType 1 3 0]

def addressType {N : ℕ} (x : ProfileAddress N) (j : Fin (2 * N)) : Fin 3 → Fin 5 := fun i ↦ x i j

def profileMultiplicity (alpha beta gamma delta : ℕ) : Fin 8 → ℕ := ![alpha, beta, gamma, delta, delta, gamma, beta, alpha]

def marginalMultiplicity (N alpha beta gamma delta : ℕ) : Fin 3 → Fin 5 → ℕ := ![![N, N, 0, 0, 0], ![alpha + delta, beta + gamma, beta + gamma, alpha + delta, 0], ![alpha, beta + delta, 2 * gamma, beta + delta, alpha]]

def CoordinatewiseSupported {N : ℕ} (x : ProfileAddress N) : Prop := ∀ j, ∃ r : Fin 8, addressType x j = pattern r

def MarginalAddress (N alpha beta gamma delta : ℕ) : Type := {x : ProfileAddress N // CoordinatewiseSupported x ∧ ∀ i : Fin 3, ∀ k : Fin 5, ((Finset.univ : Finset (Fin (2 * N))).filter (fun j ↦ x i j = k)).card = marginalMultiplicity N alpha beta gamma delta i k}

def ExactProfileAddress (N alpha beta gamma delta : ℕ) : Type := {x : MarginalAddress N alpha beta gamma delta // ∀ r : Fin 8, ((Finset.univ : Finset (Fin (2 * N))).filter (fun j ↦ addressType (Subtype.val x) j = pattern r)).card = profileMultiplicity alpha beta gamma delta r}

noncomputable def fineSourceObj (K : Type u) [Field K] (q : ℕ) : Fin 8 → TensorObj K 3 := ![Phi116.cwFourthFineBlockObj K q 0 0 4 1 3 0, Phi116.cwFourthFineBlockObj K q 0 1 3 1 2 1, Phi116.cwFourthFineBlockObj K q 0 2 2 1 1 2, Phi116.cwFourthFineBlockObj K q 0 3 1 1 0 3, Phi116.cwFourthFineBlockObj K q 1 0 3 0 3 1, Phi116.cwFourthFineBlockObj K q 1 1 2 0 2 2, Phi116.cwFourthFineBlockObj K q 1 2 1 0 1 3, Phi116.cwFourthFineBlockObj K q 1 3 0 0 0 4]

noncomputable def componentObj (K : Type u) [Field K] (q : ℕ) : Fin 8 → TensorObj K 3 := ![MMObj K 1 (2 * q) 1, TensorObj.kron (MMObj K 1 1 (2 * q)) (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)), TensorObj.kron (MMObj K 1 1 (q ^ 2 + 2)) (coupledObj K q), MMObj K (2 * q) 1 (2 * q), MMObj K (2 * q) 1 (2 * q), TensorObj.kron (coupledObj K q) (MMObj K 1 1 (q ^ 2 + 2)), TensorObj.kron (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)) (MMObj K 1 1 (2 * q)), MMObj K 1 (2 * q) 1]

end MME.StothersFourth.Phi134

/- Inlined legacy definition module: Def_mme_stothers_phi134_cyclic_hash_data. -/
open BigOperators

namespace MME.StothersFourth.Phi134

set_option autoImplicit false

/-- Three cyclic copies of the exact `phi_134` profile family.  Marginal
injectivity makes this also the full same-marginal family. -/
def CyclicExactEdge
    (N alpha beta gamma delta : ℕ) : Type :=
  ExactProfileAddress N alpha beta gamma delta ×
    (ExactProfileAddress N alpha beta gamma delta ×
      ExactProfileAddress N alpha beta gamma delta)

/-- A cyclic vertex records one mode word from each of the three copies. -/
abbrev CyclicModeWord (N : ℕ) : Type :=
  MME.StothersFourth.Phi233.CyclicModeWord N

/-- The three cyclic vertex projections, in the order
`(A₀,B₂,C₁)`, `(A₁,B₀,C₂)`, `(A₂,B₁,C₀)`. -/
def cyclicModeWord
    {N alpha beta gamma delta : ℕ}
    (e : CyclicExactEdge N alpha beta gamma delta) :
    Fin 3 → CyclicModeWord N
  | ⟨0, _⟩ =>
      (e.1.1.1 0, (e.2.1.1.1 2, e.2.2.1.1 1))
  | ⟨1, _⟩ =>
      (e.1.1.1 1, (e.2.1.1.1 0, e.2.2.1.1 2))
  | ⟨2, _⟩ =>
      (e.1.1.1 2, (e.2.1.1.1 1, e.2.2.1.1 0))
  | ⟨n + 3, h⟩ => absurd h (by omega)

/-- Form a three-mode address by taking mode zero from `x`, mode one from
`y`, and mode two from `z`. -/
def mixedAddress
    {N alpha beta gamma delta : ℕ}
    (x y z : MarginalAddress N alpha beta gamma delta) : ProfileAddress N
  | ⟨0, _⟩, j => x.1 0 j
  | ⟨1, _⟩, j => y.1 1 j
  | ⟨2, _⟩, j => z.1 2 j
  | ⟨n + 3, h⟩, _ => absurd h (by omega)

/-- Coordinatewise support of the three cyclic modewise mixtures. -/
def CyclicCoordinatewiseSupported
    {N alpha beta gamma delta : ℕ}
    (x y z : CyclicExactEdge N alpha beta gamma delta) : Prop :=
  CoordinatewiseSupported (mixedAddress x.1.1 y.1.1 z.1.1) ∧
    CoordinatewiseSupported
      (mixedAddress y.2.1.1 z.2.1.1 x.2.1.1) ∧
    CoordinatewiseSupported
      (mixedAddress z.2.2.1 x.2.2.1 y.2.2.1)

/-- A supported modewise mixture has the prescribed marginal histograms. -/
def mixedMarginalAddress
    {N alpha beta gamma delta : ℕ}
    (x y z : MarginalAddress N alpha beta gamma delta)
    (hsupport : CoordinatewiseSupported (mixedAddress x y z)) :
    MarginalAddress N alpha beta gamma delta := by
  refine ⟨mixedAddress x y z, hsupport, ?_⟩
  intro i k
  fin_cases i
  · change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ x.1 (0 : Fin 3) j = k)).card =
        marginalMultiplicity N alpha beta gamma delta (0 : Fin 3) k
    exact x.2.2 (0 : Fin 3) k
  · change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ y.1 (1 : Fin 3) j = k)).card =
        marginalMultiplicity N alpha beta gamma delta (1 : Fin 3) k
    exact y.2.2 (1 : Fin 3) k
  · change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ z.1 (2 : Fin 3) j = k)).card =
        marginalMultiplicity N alpha beta gamma delta (2 : Fin 3) k
    exact z.2.2 (2 : Fin 3) k

/-- Concrete finite enumeration of exact profile addresses. -/
@[instance_reducible]
noncomputable def exactProfileAddressFintype
    (N alpha beta gamma delta : ℕ) :
    Fintype (ExactProfileAddress N alpha beta gamma delta) :=
  @Subtype.fintype _ _ (Classical.decPred _)
    (@Subtype.fintype _ _ (Classical.decPred _) Pi.instFintype)

/-- Concrete finite enumeration of cyclic exact edges. -/
@[instance_reducible]
noncomputable def cyclicExactEdgeFintype
    (N alpha beta gamma delta : ℕ) :
    Fintype (CyclicExactEdge N alpha beta gamma delta) := by
  letI := exactProfileAddressFintype N alpha beta gamma delta
  unfold CyclicExactEdge
  infer_instance

/-- The full finite exact cyclic family. -/
noncomputable def edgeFinset
    (N alpha beta gamma delta : ℕ) :
    Finset (CyclicExactEdge N alpha beta gamma delta) := by
  letI := cyclicExactEdgeFintype N alpha beta gamma delta
  exact Finset.univ

/-- The reusable coefficient code of the cyclic type-2 hash. -/
abbrev cyclicHashModeCode
    (p N : ℕ) (i : Fin 3) (u : CyclicModeWord N) :
    Fin 3 → Fin (2 * N) → ZMod p :=
  MME.StothersFourth.Phi233.cyclicHashModeCode p N i u

/-- The cyclic affine hash in coefficient normal form.  Writing the hash in
this form makes vertex invariance and collision fibers immediate. -/
def cyclicAffineHash
    (p N alpha beta gamma delta : ℕ)
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e : CyclicExactEdge N alpha beta gamma delta) : ZMod p :=
  shift + (![0, 12 * offset, 6 * offset] : Fin 3 → ZMod p) i +
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cyclicHashModeCode p N i (cyclicModeWord e i) r j * w r j

/-- Independent random coordinates for the cyclic affine hash. -/
def HashIndex (N : ℕ) : Type :=
  (Fin 3 × Fin (2 * N)) ⊕ Unit

/-- A weight word together with the progression-offset coordinate. -/
def HashState (p N : ℕ) : Type :=
  (HashIndex N → ZMod p) × ZMod p

/-- The three coordinate rows extracted from a hash state. -/
def stateWeights {p N : ℕ} (q : HashState p N) :
    Fin 3 → Fin (2 * N) → ZMod p :=
  fun r j ↦ q.1 (Sum.inl (r, j))

/-- The common label shift stored in the extra weight coordinate. -/
def stateShift {p N : ℕ} (q : HashState p N) : ZMod p :=
  q.1 (Sum.inr ())

/-- The cyclic hash evaluated from a complete state. -/
def stateHash
    (p N alpha beta gamma delta : ℕ)
    (q : HashState p N) (i : Fin 3)
    (e : CyclicExactEdge N alpha beta gamma delta) : ZMod p :=
  cyclicAffineHash p N alpha beta gamma delta
    (stateWeights q) (stateShift q) ((6 : ZMod p)⁻¹ * q.2) i e

/-- An edge is retained when all three vertices receive one allowed label. -/
def Retained
    (p N alpha beta gamma delta : ℕ) (S : Finset (ZMod p))
    (q : HashState p N)
    (e : CyclicExactEdge N alpha beta gamma delta) : Prop :=
  ∃ s ∈ S, ∀ i : Fin 3,
    stateHash p N alpha beta gamma delta q i e = s

/-- Exact cyclic edges retained by a fixed hash state. -/
noncomputable def retainedEdges
    (p N alpha beta gamma delta : ℕ) (S : Finset (ZMod p))
    (q : HashState p N) :
    Finset (CyclicExactEdge N alpha beta gamma delta) := by
  classical
  exact (edgeFinset N alpha beta gamma delta).filter
    (Retained p N alpha beta gamma delta S q)

/-- Canonical finite enumeration of the affine hash state space. -/
noncomputable instance hashStateFintype
    (p N : ℕ) [Fact p.Prime] : Fintype (HashState p N) := by
  unfold HashState HashIndex
  infer_instance

/-- Classical decidable equality on the finite hash state space. -/
noncomputable instance hashStateDecidableEq
    (p N : ℕ) : DecidableEq (HashState p N) :=
  Classical.decEq _

end MME.StothersFourth.Phi134

/- Inlined legacy definition module: Def_mme_stothers_phi134_exact_label. -/
open MME

namespace MME.StothersFourth.Phi134

set_option autoImplicit false

noncomputable def exactLabelAt
    {N alpha beta gamma delta : ℕ}
    (x : ExactProfileAddress N alpha beta gamma delta)
    (j : Fin (2 * N)) : Fin 8 :=
  Classical.choose (x.1.2.1 j)

@[simp] theorem addressType_exactLabelAt
    {N alpha beta gamma delta : ℕ}
    (x : ExactProfileAddress N alpha beta gamma delta)
    (j : Fin (2 * N)) :
    addressType x.1.1 j = pattern (exactLabelAt x j) :=
  Classical.choose_spec (x.1.2.1 j)

end MME.StothersFourth.Phi134

/- Inlined legacy definition module: Def_mme_stothers_phi134_outer_grading. -/
open MME Module

namespace MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def modeTotalGrade (s : Fin 3) : Fin 9 := cwFourthBlockType 1 3 4 s

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

noncomputable def canonicalBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis (ModeIndex q s) K ((cwFourthConstituent K q 1 3 4).V s) := by
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

def outerGrade (q : ℕ) (s : Fin 3) (p : ModeIndex q s) : Fin 5 :=
  cwSquarePairGrade q p.1.1

noncomputable def outerGrading
    (K : Type u) [Field K] (q : ℕ) :
    (cwFourthConstituent K q 1 3 4).TypeGrading 5 where
  decomp s := cwBasisGrade (canonicalBasis K q s) (outerGrade q s)
  is_internal s := cwBasisGrade_isInternal (canonicalBasis K q s) (outerGrade q s)

end MME.StothersFourth.Phi134

/- Inlined legacy definition module: Def_mme_stothers_phi134_cyclic_grading_address. -/
open MME

namespace MME.StothersFourth.Phi134

set_option autoImplicit false

def cyclicGradingAddress
    {N alpha beta gamma delta : ℕ}
    (e : CyclicExactEdge N alpha beta gamma delta)
    (i : Fin 3) (j : Fin (2 * N)) : Fin (5 * (5 * 5)) :=
  mmeCyclicTripleGrade
    (fun s ↦ e.1.1.1 s j)
    (fun s ↦ e.2.1.1.1 s j)
    (fun s ↦ e.2.2.1.1 s j) i

end MME.StothersFourth.Phi134

/- Inlined accepted legacy proof: mme_stothers_phi134_fixed_mode_exact_profile_fiber_card. -/
open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

private theorem inline_fixed_mode_exact_profile_fiber_card_phi134_pattern_injective : Function.Injective pattern := by
  intro r s h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  fin_cases r <;> fin_cases s <;>
    simp [pattern, MME.cwSquareBlockType] at h0 h1 h2 ⊢

private noncomputable def phi134_addressLabel
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) : Fin 8 :=
  Classical.choose (hx j)

private theorem inline_fixed_mode_exact_profile_fiber_card_phi134_addressLabel_spec
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) :
    addressType x j = pattern (phi134_addressLabel x hx j) :=
  Classical.choose_spec (hx j)

private theorem inline_fixed_mode_exact_profile_fiber_card_phi134_projectedFiberCard
    {N : ℕ} (g : Fin (2 * N) → Fin 8) (i : Fin 3) (s : Fin 5) :
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ pattern (g j) i = s)).card =
      ∑ r : {r : Fin 8 // pattern r i = s},
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ g j = r.1)).card := by
  classical
  let e :
      {j : Fin (2 * N) // pattern (g j) i = s} ≃
        Sigma fun r : {r : Fin 8 // pattern r i = s} ↦
          {j : Fin (2 * N) // g j = r.1} := {
    toFun j := ⟨⟨g j.1, j.2⟩, ⟨j.1, rfl⟩⟩
    invFun x := ⟨x.2.1, by
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
  intro r _hr
  rw [← Fintype.card_subtype]

private theorem inline_fixed_mode_exact_profile_fiber_card_phi134_sum_ite_eq_sum_subtype
    {beta iota M : Type*} [Fintype beta] [DecidableEq iota]
    [AddCommMonoid M] (q : beta → iota) (i : iota) (f : beta → M) :
    (∑ b : beta, if q b = i then f b else 0) =
      ∑ b : {b : beta // q b = i}, f b.1 := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    ((Finset.univ : Finset beta).filter (fun b ↦ q b = i))
    (fun b ↦ by simp) f

theorem mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N)
    (w : ExactProfileAddress N alpha beta gamma delta)
    (i : Fin 3) :
    Nat.card
        {v : ExactProfileAddress N alpha beta gamma delta //
          v.1.1 i = w.1.1 i} =
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 8 // pattern r i = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial := by
  classical
  let multiplicity : Fin 8 → ℕ :=
    profileMultiplicity alpha beta gamma delta
  let Assignment :=
    {g : Fin (2 * N) → Fin 8 //
      (∀ j, pattern (g j) i = w.1.1 i j) ∧
      ∀ r, Fintype.card {j // g j = r} = multiplicity r}
  let Fiber :=
    {v : ExactProfileAddress N alpha beta gamma delta //
      v.1.1 i = w.1.1 i}
  have hprofileSum (l : Fin 3) (s : Fin 5) :
      (∑ r : {r : Fin 8 // pattern r l = s}, multiplicity r.1) =
        marginalMultiplicity N alpha beta gamma delta l s := by
    rw [← inline_fixed_mode_exact_profile_fiber_card_phi134_sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r l) s multiplicity]
    fin_cases l <;> fin_cases s <;>
      simp [multiplicity, pattern, profileMultiplicity,
        marginalMultiplicity, MME.cwSquareBlockType,
        Fin.sum_univ_succ] <;> omega
  let e : Fiber ≃ Assignment := {
    toFun v := ⟨fun j ↦ phi134_addressLabel v.1.1.1 v.1.1.2.1 j, by
      constructor
      · intro j
        have hj := congrFun
          (inline_fixed_mode_exact_profile_fiber_card_phi134_addressLabel_spec v.1.1.1 v.1.1.2.1 j) i
        exact hj.symm.trans (congrFun v.2 j)
      · intro r
        rw [Fintype.card_subtype]
        change _ = profileMultiplicity alpha beta gamma delta r
        rw [← v.1.2 r]
        apply congrArg Finset.card
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hj
          exact (inline_fixed_mode_exact_profile_fiber_card_phi134_addressLabel_spec v.1.1.1 v.1.1.2.1 j).trans
            (congrArg pattern hj)
        · intro hj
          apply inline_fixed_mode_exact_profile_fiber_card_phi134_pattern_injective
          exact (inline_fixed_mode_exact_profile_fiber_card_phi134_addressLabel_spec v.1.1.1 v.1.1.2.1 j).symm.trans hj⟩
    invFun G := by
      let x : ProfileAddress N := fun l j ↦ pattern (G.1 j) l
      have hxSupport : CoordinatewiseSupported x := by
        intro j
        exact ⟨G.1 j, rfl⟩
      have hxMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
          ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ x l j = s)).card =
              marginalMultiplicity N alpha beta gamma delta l s := by
        intro l s
        change ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ pattern (G.1 j) l = s)).card = _
        rw [inline_fixed_mode_exact_profile_fiber_card_phi134_projectedFiberCard]
        calc
          (∑ r : {r : Fin 8 // pattern r l = s},
              ((Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ G.1 j = r.1)).card) =
              ∑ r : {r : Fin 8 // pattern r l = s},
                multiplicity r.1 := by
                  apply Finset.sum_congr rfl
                  intro r _hr
                  rw [← Fintype.card_subtype]
                  exact G.2.2 r.1
          _ = marginalMultiplicity N alpha beta gamma delta l s :=
            hprofileSum l s
      let xm : MarginalAddress N alpha beta gamma delta :=
        ⟨x, hxSupport, hxMarginal⟩
      let xe : ExactProfileAddress N alpha beta gamma delta := ⟨xm, by
        intro r
        have hset :
            (Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ addressType x j = pattern r) =
              (Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ G.1 j = r) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          change pattern (G.1 j) = pattern r ↔ G.1 j = r
          exact ⟨(fun h ↦ inline_fixed_mode_exact_profile_fiber_card_phi134_pattern_injective h), congrArg pattern⟩
        rw [hset, ← Fintype.card_subtype]
        exact G.2.2 r⟩
      refine ⟨xe, ?_⟩
      funext j
      exact G.2.1 j
    left_inv v := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext l j
      exact (congrFun
        (inline_fixed_mode_exact_profile_fiber_card_phi134_addressLabel_spec v.1.1.1 v.1.1.2.1 j) l).symm
    right_inv G := by
      apply Subtype.ext
      funext j
      apply inline_fixed_mode_exact_profile_fiber_card_phi134_pattern_injective
      exact
        (inline_fixed_mode_exact_profile_fiber_card_phi134_addressLabel_spec
          (fun l j ↦ pattern (G.1 j) l) (fun j ↦ ⟨G.1 j, rfl⟩) j).symm.trans (by
            funext l
            rfl)
  }
  have hmarginal : ∀ l : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ w.1.1 l j = s)).card =
          marginalMultiplicity N alpha beta gamma delta l s :=
    w.1.2.2
  have hconstraint (s : Fin 5) :
      (∑ r : {r : Fin 8 // pattern r i = s}, multiplicity r.1) =
        Fintype.card {j : Fin (2 * N) // w.1.1 i j = s} := by
    rw [hprofileSum i s, Fintype.card_subtype, hmarginal i s]
  have hassignment :
      Nat.card Assignment =
        ∏ s : Fin 5,
          (Fintype.card {j : Fin (2 * N) // w.1.1 i j = s}).factorial /
            ∏ r : {r : Fin 8 // pattern r i = s},
              (multiplicity r.1).factorial := by
    simpa only [Assignment] using
      (mme_fintype_constrained_prescribed_fiber_function_card
        (h := w.1.1 i) (q := fun r : Fin 8 ↦ pattern r i)
        multiplicity hconstraint)
  calc
    Nat.card
        {v : ExactProfileAddress N alpha beta gamma delta //
          v.1.1 i = w.1.1 i} = Nat.card Fiber := rfl
    _ = Nat.card Assignment := Nat.card_congr e
    _ = ∏ s : Fin 5,
        (Fintype.card {j : Fin (2 * N) // w.1.1 i j = s}).factorial /
          ∏ r : {r : Fin 8 // pattern r i = s},
            (multiplicity r.1).factorial := hassignment
    _ = ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 8 // pattern r i = s},
            (multiplicity r.1).factorial := by
      apply Finset.prod_congr rfl
      intro s _hs
      rw [Fintype.card_subtype, hmarginal i s]
    _ = ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 8 // pattern r i = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial := rfl

/- Inlined accepted legacy proof: mme_stothers_phi134_cyclic_mode_fiber_card. -/
open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

private def inline_cyclic_mode_fiber_card_phi134TripleFiberEquiv
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

theorem mme_stothers_phi134_cyclic_mode_fiber_card
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N)
    (e : CyclicExactEdge N alpha beta gamma delta)
    (i : Fin 3) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    Nat.card
        {f : CyclicExactEdge N alpha beta gamma delta //
          cyclicModeWord f i = cyclicModeWord e i} =
      D 0 * (D 1 * D 2) := by
  dsimp only
  let A := ExactProfileAddress N alpha beta gamma delta
  fin_cases i
  · let equiv := inline_cyclic_mode_fiber_card_phi134TripleFiberEquiv
      (fun w : A ↦ w.1.1 0) (fun w : A ↦ w.1.1 2)
      (fun w : A ↦ w.1.1 1) e.1 e.2.1 e.2.2
    change Nat.card
      {p : A × (A × A) //
        (p.1.1.1 0, (p.2.1.1.1 2, p.2.2.1.1 1)) =
          (e.1.1.1 0, (e.2.1.1.1 2, e.2.2.1.1 1))} = _
    rw [Nat.card_congr equiv, Nat.card_prod, Nat.card_prod]
    rw [mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.1 0,
      mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.2.1 2,
      mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.2.2 1]
    ring
  · let equiv := inline_cyclic_mode_fiber_card_phi134TripleFiberEquiv
      (fun w : A ↦ w.1.1 1) (fun w : A ↦ w.1.1 0)
      (fun w : A ↦ w.1.1 2) e.1 e.2.1 e.2.2
    change Nat.card
      {p : A × (A × A) //
        (p.1.1.1 1, (p.2.1.1.1 0, p.2.2.1.1 2)) =
          (e.1.1.1 1, (e.2.1.1.1 0, e.2.2.1.1 2))} = _
    rw [Nat.card_congr equiv, Nat.card_prod, Nat.card_prod]
    rw [mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.1 1,
      mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.2.1 0,
      mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.2.2 2]
    ring
  · let equiv := inline_cyclic_mode_fiber_card_phi134TripleFiberEquiv
      (fun w : A ↦ w.1.1 2) (fun w : A ↦ w.1.1 1)
      (fun w : A ↦ w.1.1 0) e.1 e.2.1 e.2.2
    change Nat.card
      {p : A × (A × A) //
        (p.1.1.1 2, (p.2.1.1.1 1, p.2.2.1.1 0)) =
          (e.1.1.1 2, (e.2.1.1.1 1, e.2.2.1.1 0))} = _
    rw [Nat.card_congr equiv, Nat.card_prod, Nat.card_prod]
    rw [mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.1 2,
      mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.2.1 1,
      mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma delta hsum e.2.2 0]
    ring

/- Inlined accepted legacy proof: mme_stothers_phi134_exact_profile_card. -/
open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace MME.StothersFourth.Phi134ExactCard

private theorem inline_exact_profile_card_pattern_injective : Function.Injective pattern := by
  intro r s h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  fin_cases r <;> fin_cases s <;>
    simp [pattern, MME.cwSquareBlockType] at h0 h1 h2 ⊢

private noncomputable def addressLabel
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) : Fin 8 :=
  Classical.choose (hx j)

private theorem inline_exact_profile_card_addressLabel_spec
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) :
    addressType x j = pattern (addressLabel x hx j) :=
  Classical.choose_spec (hx j)

private theorem inline_exact_profile_card_projectedFiberCard
    {N : ℕ} (g : Fin (2 * N) → Fin 8) (i : Fin 3) (s : Fin 5) :
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ pattern (g j) i = s)).card =
      ∑ r : {r : Fin 8 // pattern r i = s},
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ g j = r.1)).card := by
  classical
  let e :
      {j : Fin (2 * N) // pattern (g j) i = s} ≃
        Sigma fun r : {r : Fin 8 // pattern r i = s} ↦
          {j : Fin (2 * N) // g j = r.1} := {
    toFun j := ⟨⟨g j.1, j.2⟩, ⟨j.1, rfl⟩⟩
    invFun x := ⟨x.2.1, by
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
  intro r _hr
  rw [← Fintype.card_subtype]

private theorem inline_exact_profile_card_sum_ite_eq_sum_subtype
    {beta iota M : Type*} [Fintype beta] [DecidableEq iota]
    [AddCommMonoid M] (q : beta → iota) (i : iota) (f : beta → M) :
    (∑ b : beta, if q b = i then f b else 0) =
      ∑ b : {b : beta // q b = i}, f b.1 := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    ((Finset.univ : Finset beta).filter (fun b ↦ q b = i))
    (fun b ↦ by simp) f

private theorem inline_exact_profile_card_profile_sum
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N)
    (l : Fin 3) (s : Fin 5) :
    (∑ r : {r : Fin 8 // pattern r l = s},
        profileMultiplicity alpha beta gamma delta r.1) =
      marginalMultiplicity N alpha beta gamma delta l s := by
  rw [← inline_exact_profile_card_sum_ite_eq_sum_subtype
    (fun r : Fin 8 ↦ pattern r l) s
      (profileMultiplicity alpha beta gamma delta)]
  fin_cases l <;> fin_cases s <;>
    simp [pattern, profileMultiplicity, marginalMultiplicity,
      MME.cwSquareBlockType, Fin.sum_univ_succ] <;> omega

end MME.StothersFourth.Phi134ExactCard

/-- Development form of the exact symmetric eight-pattern cardinality. -/
theorem mme_stothers_phi134_exact_profile_card_local
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    Nat.card
        (ExactProfileAddress N alpha beta gamma delta) =
      (2 * N).factorial /
        ∏ r : Fin 8,
          (profileMultiplicity alpha beta gamma delta r).factorial := by
  classical
  let multiplicity : Fin 8 → ℕ :=
    profileMultiplicity alpha beta gamma delta
  have htotal : (∑ r : Fin 8, multiplicity r) = 2 * N := by
    simp [multiplicity, profileMultiplicity, Fin.sum_univ_succ]
    omega
  have htotalCard :
      (∑ r : Fin 8, multiplicity r) = Fintype.card (Fin (2 * N)) := by
    simpa using htotal
  let Assignment :=
    {g : Fin (2 * N) → Fin 8 //
      ∀ r, Fintype.card {j // g j = r} = multiplicity r}
  let ftGeneric : Fintype Assignment :=
    @Subtype.fintype _ _
      (fun _ => Fintype.decidableForallFintype) Pi.instFintype
  have hgeneric :
      @Fintype.card Assignment ftGeneric =
        (2 * N).factorial / ∏ r : Fin 8, (multiplicity r).factorial := by
    simpa only [Assignment, Fintype.card_fin] using
      (mme_fintype_prescribed_fiber_function_card
        (α := Fin (2 * N)) (ι := Fin 8) multiplicity htotalCard)
  let e : ExactProfileAddress N alpha beta gamma delta ≃ Assignment := {
    toFun w := ⟨fun j ↦
      MME.StothersFourth.Phi134ExactCard.addressLabel
        w.1.1 w.1.2.1 j, by
      intro r
      rw [Fintype.card_subtype]
      change _ = profileMultiplicity alpha beta gamma delta r
      rw [← w.2 r]
      apply congrArg Finset.card
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        exact (MME.StothersFourth.Phi134ExactCard.inline_exact_profile_card_addressLabel_spec
          w.1.1 w.1.2.1 j).trans (congrArg pattern hj)
      · intro hj
        apply MME.StothersFourth.Phi134ExactCard.inline_exact_profile_card_pattern_injective
        exact (MME.StothersFourth.Phi134ExactCard.inline_exact_profile_card_addressLabel_spec
          w.1.1 w.1.2.1 j).symm.trans hj⟩
    invFun G := by
      let x : ProfileAddress N := fun l j ↦ pattern (G.1 j) l
      have hxSupport : CoordinatewiseSupported x := by
        intro j
        exact ⟨G.1 j, rfl⟩
      have hxMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
          ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ x l j = s)).card =
              marginalMultiplicity N alpha beta gamma delta l s := by
        intro l s
        change ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ pattern (G.1 j) l = s)).card = _
        rw [MME.StothersFourth.Phi134ExactCard.inline_exact_profile_card_projectedFiberCard]
        calc
          (∑ r : {r : Fin 8 // pattern r l = s},
              ((Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ G.1 j = r.1)).card) =
              ∑ r : {r : Fin 8 // pattern r l = s},
                multiplicity r.1 := by
                  apply Finset.sum_congr rfl
                  intro r _hr
                  rw [← Fintype.card_subtype]
                  exact G.2 r.1
          _ = marginalMultiplicity N alpha beta gamma delta l s :=
            MME.StothersFourth.Phi134ExactCard.inline_exact_profile_card_profile_sum
              N alpha beta gamma delta hsum l s
      let xm : MarginalAddress N alpha beta gamma delta :=
        ⟨x, hxSupport, hxMarginal⟩
      exact ⟨xm, by
        intro r
        have hset :
            (Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ addressType x j = pattern r) =
              (Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ G.1 j = r) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          change pattern (G.1 j) = pattern r ↔ G.1 j = r
          exact ⟨
            fun h ↦ MME.StothersFourth.Phi134ExactCard.inline_exact_profile_card_pattern_injective h,
            congrArg pattern⟩
        rw [hset, ← Fintype.card_subtype]
        exact G.2 r⟩
    left_inv w := by
      apply Subtype.ext
      apply Subtype.ext
      funext l j
      exact (congrFun
        (MME.StothersFourth.Phi134ExactCard.inline_exact_profile_card_addressLabel_spec
          w.1.1 w.1.2.1 j) l).symm
    right_inv G := by
      apply Subtype.ext
      funext j
      apply MME.StothersFourth.Phi134ExactCard.inline_exact_profile_card_pattern_injective
      exact
        (MME.StothersFourth.Phi134ExactCard.inline_exact_profile_card_addressLabel_spec
          (fun l j ↦ pattern (G.1 j) l)
          (fun j ↦ ⟨G.1 j, rfl⟩) j).symm.trans (by
            funext l
            rfl)
  }
  calc
    Nat.card (ExactProfileAddress N alpha beta gamma delta) =
        Nat.card Assignment := Nat.card_congr e
    _ = @Fintype.card Assignment inferInstance := Nat.card_eq_fintype_card
    _ = @Fintype.card Assignment ftGeneric :=
      @Fintype.card_congr Assignment Assignment inferInstance ftGeneric
        (Equiv.refl Assignment)
    _ = (2 * N).factorial /
        ∏ r : Fin 8, (multiplicity r).factorial := hgeneric
    _ = (2 * N).factorial /
        ∏ r : Fin 8,
          (profileMultiplicity alpha beta gamma delta r).factorial := rfl

/-- The number of exact symmetric eight-pattern Phi134 profile addresses. -/
theorem mme_stothers_phi134_exact_profile_card
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    Nat.card
        (ExactProfileAddress N alpha beta gamma delta) =
      (2 * N).factorial /
        ∏ r : Fin 8,
          (profileMultiplicity alpha beta gamma delta r).factorial := by
  exact mme_stothers_phi134_exact_profile_card_local
    N alpha beta gamma delta hsum

/- Inlined accepted legacy proof: mme_stothers_phi134_cyclic_degree_bounds. -/
open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true

namespace MME.StothersFourth.Phi134DegreeBounds

private noncomputable def addressLabel
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) : Fin 8 :=
  Classical.choose (hx j)

private theorem inline_cyclic_degree_bounds_addressLabel_spec
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) :
    addressType x j = pattern (addressLabel x hx j) :=
  Classical.choose_spec (hx j)

private theorem inline_cyclic_degree_bounds_pattern_injective : Function.Injective pattern := by
  intro r s h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  fin_cases r <;> fin_cases s <;>
    simp [pattern, MME.cwSquareBlockType] at h0 h1 h2 ⊢

private theorem inline_cyclic_degree_bounds_label_injective
    (N alpha beta gamma delta : ℕ) :
    Function.Injective
      (fun w : ExactProfileAddress N alpha beta gamma delta ↦
        fun j ↦ addressLabel w.1.1 w.1.2.1 j) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  have hsx := congrFun (inline_cyclic_degree_bounds_addressLabel_spec x.1.1 x.1.2.1 j) i
  have hsy := congrFun (inline_cyclic_degree_bounds_addressLabel_spec y.1.1 y.1.2.1 j) i
  have hj := congrFun h j
  exact hsx.trans
    ((congrArg (fun r ↦ pattern r i) hj).trans hsy.symm)

private theorem inline_cyclic_degree_bounds_profile_total
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    ∑ r : Fin 8, profileMultiplicity alpha beta gamma delta r = 2 * N := by
  simp [profileMultiplicity, Fin.sum_univ_succ]
  omega

end MME.StothersFourth.Phi134DegreeBounds

/-- The sharp cyclic same-mode degree is positive and bounded by the
exponential envelope used by the prime--Behrend selector. -/
theorem mme_stothers_phi134_cyclic_degree_bounds
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    1 ≤ D 0 * (D 1 * D 2) ∧
      D 0 * (D 1 * D 2) ≤ 5 ^ (12 * N) := by
  classical
  dsimp only
  let degree : ℕ :=
    (∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta 0 s).factorial /
          ∏ r : {r : Fin 8 // pattern r 0 = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial) *
      ((∏ s : Fin 5,
          (marginalMultiplicity N alpha beta gamma delta 1 s).factorial /
            ∏ r : {r : Fin 8 // pattern r 1 = s},
              (profileMultiplicity alpha beta gamma delta r.1).factorial) *
        (∏ s : Fin 5,
          (marginalMultiplicity N alpha beta gamma delta 2 s).factorial /
            ∏ r : {r : Fin 8 // pattern r 2 = s},
              (profileMultiplicity alpha beta gamma delta r.1).factorial))
  letI : Fintype (ExactProfileAddress N alpha beta gamma delta) :=
    exactProfileAddressFintype N alpha beta gamma delta
  letI : Fintype (CyclicExactEdge N alpha beta gamma delta) :=
    cyclicExactEdgeFintype N alpha beta gamma delta
  have htarget : 0 < Nat.card
      (ExactProfileAddress N alpha beta gamma delta) := by
    rw [mme_stothers_phi134_exact_profile_card
      N alpha beta gamma delta hsum]
    have hh := Nat.multinomial_pos Finset.univ
      (profileMultiplicity alpha beta gamma delta)
    simpa only [Nat.multinomial,
      MME.StothersFourth.Phi134DegreeBounds.inline_cyclic_degree_bounds_profile_total
        N alpha beta gamma delta hsum] using hh
  obtain ⟨w⟩ := (Nat.card_pos_iff.mp htarget).1
  let e : CyclicExactEdge N alpha beta gamma delta := (w, (w, w))
  let F := {f : CyclicExactEdge N alpha beta gamma delta //
    cyclicModeWord f 0 = cyclicModeWord e 0}
  have heq : Nat.card F = degree := by
    have h := mme_stothers_phi134_cyclic_mode_fiber_card
      N alpha beta gamma delta hsum e 0
    simpa only [F, degree] using h
  have hpos : 0 < Nat.card F :=
    (Nat.card_pos_iff).mpr ⟨⟨⟨e, rfl⟩⟩, inferInstance⟩
  have hle : Nat.card F ≤
      Nat.card (CyclicExactEdge N alpha beta gamma delta) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hw : Nat.card (ExactProfileAddress N alpha beta gamma delta) ≤
      8 ^ (2 * N) := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (ExactProfileAddress N alpha beta gamma delta) ≤
          Fintype.card (Fin (2 * N) → Fin 8) :=
        Fintype.card_le_of_injective
          (fun w j ↦
            MME.StothersFourth.Phi134DegreeBounds.addressLabel
              w.1.1 w.1.2.1 j)
          (MME.StothersFourth.Phi134DegreeBounds.inline_cyclic_degree_bounds_label_injective
            N alpha beta gamma delta)
      _ = 8 ^ (2 * N) := by simp
  have hc : Nat.card (CyclicExactEdge N alpha beta gamma delta) =
      (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 := by
    simp [CyclicExactEdge, pow_succ]
    ring
  change 1 ≤ degree ∧ degree ≤ 5 ^ (12 * N)
  refine ⟨by rw [← heq]; omega, ?_⟩
  rw [← heq]
  calc
    Nat.card F ≤ Nat.card
        (CyclicExactEdge N alpha beta gamma delta) := hle
    _ ≤ (8 ^ (2 * N)) ^ 3 := by
      rw [hc]
      exact Nat.pow_le_pow_left hw 3
    _ = 8 ^ (6 * N) := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ 25 ^ (6 * N) := Nat.pow_le_pow_left (by omega) _
    _ = 5 ^ (12 * N) := by
      rw [show (25 : ℕ) = 5 ^ 2 by norm_num, ← pow_mul]
      congr 1
      omega

/- Inlined accepted legacy proof: mme_stothers_phi134_behrend_prime_of_cyclic_degree. -/
open MME BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

/-- A prime and progression-free label set large enough for the sharp
Phi134 cyclic collision degree, with the explicit subexponential bound. -/
theorem mme_stothers_phi134_behrend_prime_of_cyclic_degree
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    ∃ p : ℕ, Nat.Prime p ∧ 7 ≤ p ∧
      ∃ S : Finset (ZMod p),
        (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
          x + y = 2 * z → x = z ∧ z = y) ∧
        6 * (D 0 * (D 1 * D 2) : ℝ) ≤ S.card ∧
        (p : ℝ) ≤ (D 0 * (D 1 * D 2) : ℝ) *
          Real.exp (2000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ)) := by
  classical
  dsimp only
  let degree : ℕ :=
    (∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta 0 s).factorial /
          ∏ r : {r : Fin 8 // pattern r 0 = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial) *
      ((∏ s : Fin 5,
          (marginalMultiplicity N alpha beta gamma delta 1 s).factorial /
            ∏ r : {r : Fin 8 // pattern r 1 = s},
              (profileMultiplicity alpha beta gamma delta r.1).factorial) *
        (∏ s : Fin 5,
          (marginalMultiplicity N alpha beta gamma delta 2 s).factorial /
            ∏ r : {r : Fin 8 // pattern r 2 = s},
              (profileMultiplicity alpha beta gamma delta r.1).factorial))
  have hbounds := mme_stothers_phi134_cyclic_degree_bounds
    N alpha beta gamma delta hsum
  change 1 ≤ degree ∧ degree ≤ 5 ^ (12 * N) at hbounds
  obtain ⟨p, hp, hp5, Sold, hSrange, hSfree, hSbig, hpbound⟩ :=
    mme_prime_behrend_dominates_bounded_collision_degree
      (12 * N) degree hbounds.1 hbounds.2
  have hcard := Finset.card_le_card hSrange
  rw [Finset.card_range] at hcard
  have hSbigNat : 6 * degree ≤ Sold.card := by
    exact_mod_cast hSbig
  have hSix : 6 ≤ Sold.card := by omega
  have hp7 : 7 ≤ p := by omega
  obtain ⟨hcastcard, hcastfree⟩ :=
    mme_stothers_phi233_lower_half_cast_label_package
      p Sold hSrange hSfree
  refine ⟨p, hp, hp7,
    Sold.image (fun s : ℕ ↦ (s : ZMod p)), hcastfree, ?_, ?_⟩
  · rw [hcastcard]
    simp only [degree, Nat.cast_mul] at hSbig
    exact hSbig
  · simp only [degree, Nat.cast_mul] at hpbound
    exact hpbound

/- Inlined accepted legacy proof: mme_stothers_phi134_capacity_identity. -/
open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true

namespace MME.StothersFourth.Phi134CapacitySubmission

private noncomputable def modeDegree
    (N alpha beta gamma delta : ℕ) (i : Fin 3) : ℕ :=
  ∏ s : Fin 5,
      (marginalMultiplicity N alpha beta gamma delta i s).factorial /
    ∏ r : {r : Fin 8 // pattern r i = s},
      (profileMultiplicity alpha beta gamma delta r.1).factorial

private noncomputable def degree
    (N alpha beta gamma delta : ℕ) : ℕ :=
  modeDegree N alpha beta gamma delta 0 *
    (modeDegree N alpha beta gamma delta 1 *
      modeDegree N alpha beta gamma delta 2)

private theorem inline_capacity_identity_count_totals
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    ∑ r : Fin 8, profileMultiplicity alpha beta gamma delta r = 2 * N := by
  simp [Fin.sum_univ_succ, profileMultiplicity]
  omega

private theorem inline_capacity_identity_marginal_totals
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) (i : Fin 3) :
    ∑ s : Fin 5, marginalMultiplicity N alpha beta gamma delta i s =
      2 * N := by
  fin_cases i <;>
    simp [Fin.sum_univ_succ, marginalMultiplicity] <;> omega

private theorem inline_capacity_identity_cell_counts
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N)
    (i : Fin 3) (s : Fin 5) :
    ∑ r : {r : Fin 8 // pattern r i = s},
        profileMultiplicity alpha beta gamma delta r.1 =
      marginalMultiplicity N alpha beta gamma delta i s := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun r : Fin 8 ↦ pattern r i = s))
    (by intro r; simp) (profileMultiplicity alpha beta gamma delta)]
  rw [Finset.sum_filter]
  fin_cases i <;> fin_cases s <;>
    norm_num [Fin.sum_univ_succ, Fin.reduceFinMk, Fin.succ,
      profileMultiplicity, marginalMultiplicity, pattern,
      MME.cwSquareBlockType] <;>
    norm_num [Fin.ext_iff] <;> omega

private theorem inline_capacity_identity_mode_factorization
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) (i : Fin 3) :
    Nat.card (ExactProfileAddress N alpha beta gamma delta) =
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (marginalMultiplicity N alpha beta gamma delta i s).factorial) *
        modeDegree N alpha beta gamma delta i := by
  classical
  let J := ∏ r : Fin 8,
    (profileMultiplicity alpha beta gamma delta r).factorial
  let M := ∏ s : Fin 5,
    (marginalMultiplicity N alpha beta gamma delta i s).factorial
  have hc (s : Fin 5) :
      (∏ r : {r : Fin 8 // pattern r i = s},
          (profileMultiplicity alpha beta gamma delta r.1).factorial) *
        ((marginalMultiplicity N alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 8 // pattern r i = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial) =
      (marginalMultiplicity N alpha beta gamma delta i s).factorial := by
    have hh := Nat.multinomial_spec Finset.univ
      (fun r : {r : Fin 8 // pattern r i = s} ↦
        profileMultiplicity alpha beta gamma delta r.1)
    simpa only [Nat.multinomial,
      inline_capacity_identity_cell_counts N alpha beta gamma delta hsum i s] using hh
  have hprod := congrArg (fun f : Fin 5 → ℕ ↦ ∏ s, f s) (funext hc)
  simp only [Finset.prod_mul_distrib] at hprod
  rw [Fintype.prod_fiberwise (fun r : Fin 8 ↦ pattern r i)
    (fun r ↦ (profileMultiplicity alpha beta gamma delta r).factorial)]
      at hprod
  change J * modeDegree N alpha beta gamma delta i = M at hprod
  have hrow := Nat.multinomial_spec Finset.univ
    (marginalMultiplicity N alpha beta gamma delta i)
  simp only [Nat.multinomial,
    inline_capacity_identity_marginal_totals N alpha beta gamma delta hsum i] at hrow
  have hjoint := Nat.multinomial_spec Finset.univ
    (profileMultiplicity alpha beta gamma delta)
  simp only [Nat.multinomial,
    inline_capacity_identity_count_totals N alpha beta gamma delta hsum] at hjoint
  rw [mme_stothers_phi134_exact_profile_card
    N alpha beta gamma delta hsum]
  have hJ : 0 < J :=
    Finset.prod_pos (fun _ _ ↦ Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_left hJ
  change J * ((2 * N).factorial / J) =
    J * (((2 * N).factorial / M) *
      modeDegree N alpha beta gamma delta i)
  calc
    _ = (2 * N).factorial := hjoint
    _ = M * ((2 * N).factorial / M) := hrow.symm
    _ = _ := by rw [← hprod]; ac_rfl

private theorem inline_capacity_identity_capacity_identity
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    (∏ i : Fin 3,
        Nat.multinomial Finset.univ
          (marginalMultiplicity N alpha beta gamma delta i)) *
        degree N alpha beta gamma delta =
      (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 := by
  have h0 := inline_capacity_identity_mode_factorization N alpha beta gamma delta hsum 0
  have h1 := inline_capacity_identity_mode_factorization N alpha beta gamma delta hsum 1
  have h2 := inline_capacity_identity_mode_factorization N alpha beta gamma delta hsum 2
  simp only [Nat.multinomial,
    inline_capacity_identity_marginal_totals N alpha beta gamma delta hsum]
  rw [Fin.prod_univ_three]
  unfold degree
  calc
    _ =
        (((2 * N).factorial /
            ∏ s : Fin 5,
              (marginalMultiplicity N alpha beta gamma delta 0 s).factorial) *
          modeDegree N alpha beta gamma delta 0) *
        (((2 * N).factorial /
            ∏ s : Fin 5,
              (marginalMultiplicity N alpha beta gamma delta 1 s).factorial) *
          modeDegree N alpha beta gamma delta 1) *
        (((2 * N).factorial /
            ∏ s : Fin 5,
              (marginalMultiplicity N alpha beta gamma delta 2 s).factorial) *
          modeDegree N alpha beta gamma delta 2) := by ring
    _ = _ := by rw [← h0, ← h1, ← h2]; ring

end MME.StothersFourth.Phi134CapacitySubmission

/-- Three marginal multinomials times the sharp cyclic collision degree
equal the cube of the exact-profile cardinality. -/
theorem mme_stothers_phi134_capacity_identity
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    (∏ i : Fin 3,
        Nat.multinomial Finset.univ
          (marginalMultiplicity N alpha beta gamma delta i)) *
        (D 0 * (D 1 * D 2)) =
      (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 := by
  dsimp only
  simpa only [
    MME.StothersFourth.Phi134CapacitySubmission.degree,
    MME.StothersFourth.Phi134CapacitySubmission.modeDegree] using
    MME.StothersFourth.Phi134CapacitySubmission.inline_capacity_identity_capacity_identity
      N alpha beta gamma delta hsum

/- Inlined accepted legacy proof: mme_stothers_phi134_cyclic_affine_hash_AP. -/
open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

theorem mme_stothers_phi134_cyclic_affine_hash_AP
    {p N alpha beta gamma delta : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p)
    (x y z : CyclicExactEdge N alpha beta gamma delta)
    (hsupp : CyclicCoordinatewiseSupported x y z) :
    cyclicAffineHash p N alpha beta gamma delta w shift offset 0 x +
        cyclicAffineHash p N alpha beta gamma delta w shift offset 1 y =
      2 * cyclicAffineHash p N alpha beta gamma delta w shift offset 2 z := by
  have hgrade
      (a : ProfileAddress N) (ha : CoordinatewiseSupported a)
      (j : Fin (2 * N)) :
      (a 0 j).val + (a 1 j).val + (a 2 j).val = 4 := by
    obtain ⟨r, hr⟩ := ha j
    have h0 := congrFun hr (0 : Fin 3)
    have h1 := congrFun hr (1 : Fin 3)
    have h2 := congrFun hr (2 : Fin 3)
    fin_cases r <;>
      simp [addressType, pattern, MME.cwSquareBlockType] at h0 h1 h2 ⊢ <;>
      omega
  have hA (j : Fin (2 * N)) :
      (x.1.1.1 0 j).val + (y.1.1.1 1 j).val +
        (z.1.1.1 2 j).val = 4 := by
    simpa [mixedAddress] using
      hgrade (mixedAddress x.1.1 y.1.1 z.1.1) hsupp.1 j
  have hB (j : Fin (2 * N)) :
      (y.2.1.1.1 0 j).val + (z.2.1.1.1 1 j).val +
        (x.2.1.1.1 2 j).val = 4 := by
    simpa [mixedAddress] using
      hgrade (mixedAddress y.2.1.1 z.2.1.1 x.2.1.1) hsupp.2.1 j
  have hC (j : Fin (2 * N)) :
      (z.2.2.1.1 0 j).val + (x.2.2.1.1 1 j).val +
        (y.2.2.1.1 2 j).val = 4 := by
    simpa [mixedAddress] using
      hgrade (mixedAddress z.2.2.1 x.2.2.1 y.2.2.1) hsupp.2.2 j
  have haPoint (j : Fin (2 * N)) :
      ((2 * (x.1.1.1 0 j).val : ℕ) : ZMod p) * w 0 j +
          ((2 * (y.1.1.1 1 j).val : ℕ) : ZMod p) * w 0 j =
        2 * (((4 : ZMod p) - ((z.1.1.1 2 j).val : ZMod p)) * w 0 j) := by
    have hr := congrArg (fun n : ℕ ↦ (n : ZMod p)) (hA j)
    push_cast at hr ⊢
    linear_combination 2 * w 0 j * hr
  have hbPoint (j : Fin (2 * N)) :
      4 * ((4 : ZMod p) - ((x.2.1.1.1 2 j).val : ZMod p)) * w 1 j +
          (-2 * ((2 * (y.2.1.1.1 0 j).val : ℕ) : ZMod p)) * w 1 j =
        2 * (((2 * (z.2.1.1.1 1 j).val : ℕ) : ZMod p) * w 1 j) := by
    have hr := congrArg (fun n : ℕ ↦ (n : ZMod p)) (hB j)
    push_cast at hr ⊢
    linear_combination -4 * w 1 j * hr
  have hcPoint (j : Fin (2 * N)) :
      (-2 * ((2 * (x.2.2.1.1 1 j).val : ℕ) : ZMod p)) * w 2 j +
          4 * ((4 : ZMod p) - ((y.2.2.1.1 2 j).val : ZMod p)) * w 2 j =
        2 * (((2 * (z.2.2.1.1 0 j).val : ℕ) : ZMod p) * w 2 j) := by
    have hr := congrArg (fun n : ℕ ↦ (n : ZMod p)) (hC j)
    push_cast at hr ⊢
    linear_combination -4 * w 2 j * hr
  have ha :
      (∑ j, ((2 * (x.1.1.1 0 j).val : ℕ) : ZMod p) * w 0 j) +
          (∑ j, ((2 * (y.1.1.1 1 j).val : ℕ) : ZMod p) * w 0 j) =
        2 * ∑ j,
          ((4 : ZMod p) - ((z.1.1.1 2 j).val : ZMod p)) * w 0 j := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ haPoint j)
  have hb :
      (∑ j, 4 * ((4 : ZMod p) - ((x.2.1.1.1 2 j).val : ZMod p)) * w 1 j) +
          (∑ j, (-2 * ((2 * (y.2.1.1.1 0 j).val : ℕ) : ZMod p)) * w 1 j) =
        2 * ∑ j,
          ((2 * (z.2.1.1.1 1 j).val : ℕ) : ZMod p) * w 1 j := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ hbPoint j)
  have hc :
      (∑ j, (-2 * ((2 * (x.2.2.1.1 1 j).val : ℕ) : ZMod p)) * w 2 j) +
          (∑ j, 4 * ((4 : ZMod p) - ((y.2.2.1.1 2 j).val : ZMod p)) * w 2 j) =
        2 * ∑ j,
          ((2 * (z.2.2.1.1 0 j).val : ℕ) : ZMod p) * w 2 j := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ hcPoint j)
  simp [cyclicAffineHash, cyclicHashModeCode,
    MME.StothersFourth.Phi233.cyclicHashModeCode, cyclicModeWord,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
    Fin.sum_univ_succ]
  push_cast at ha hb hc ⊢
  have hbNeg :
      (∑ j, (-2 : ZMod p) * (2 * ((y.2.1.1.1 0 j).val : ZMod p)) * w 1 j) =
        -∑ j, 2 * 2 * ((y.2.1.1.1 0 j).val : ZMod p) * w 1 j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ ↦ by ring)
  have hcNeg :
      (∑ j, (-2 : ZMod p) * (2 * ((x.2.2.1.1 1 j).val : ZMod p)) * w 2 j) =
        -∑ j, 2 * 2 * ((x.2.2.1.1 1 j).val : ZMod p) * w 2 j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ ↦ by ring)
  rw [hbNeg] at hb
  rw [hcNeg] at hc
  linear_combination (norm := ring_nf) ha + hb + hc

/- Inlined accepted legacy proof: mme_stothers_phi134_cyclic_edge_retention_card. -/
open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

theorem mme_stothers_phi134_cyclic_edge_retention_card
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
    simp [H, cyclicAffineHash, weights, shift, L0]
  have hH2 (q : (I → ZMod p) × ZMod p) :
      H q 2 = shift q.1 + q.2 + L2 q.1 := by
    rw [show H q 2 =
        shift q.1 + 6 * ((6 : ZMod p)⁻¹ * q.2) + L2 q.1 by
      simp [H, cyclicAffineHash, weights, shift, L2]]
    rw [← mul_assoc, mul_inv_cancel₀ h6, one_mul]
  have hAP (q : (I → ZMod p) × ZMod p) :
      H q 0 + H q 1 = 2 * H q 2 := by
    have hmixed (a : MarginalAddress N alpha beta gamma delta) :
        mixedAddress a a a = a.1 := by
      funext i j
      fin_cases i <;> rfl
    have hsupp : CyclicCoordinatewiseSupported e e e := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hmixed]
        exact e.1.1.2.1
      · rw [hmixed]
        exact e.2.1.1.2.1
      · rw [hmixed]
        exact e.2.2.1.2.1
    exact mme_stothers_phi134_cyclic_affine_hash_AP
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

/- Inlined accepted legacy proof: mme_stothers_phi134_cyclic_mode_word_tuple_injective. -/
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

theorem mme_stothers_phi134_cyclic_mode_word_tuple_injective :
    ∀ {N alpha beta gamma delta : ℕ},
      Function.Injective
        (cyclicModeWord (N := N) (alpha := alpha) (beta := beta)
          (gamma := gamma) (delta := delta)) := by
  intro N alpha beta gamma delta e f hef
  rcases e with ⟨a, b, c⟩
  rcases f with ⟨a', b', c'⟩
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    funext i j
    fin_cases i
    · exact congrFun (congrArg Prod.fst (congrFun hef 0)) j
    · exact congrFun (congrArg Prod.fst (congrFun hef 1)) j
    · exact congrFun (congrArg Prod.fst (congrFun hef 2)) j
  · apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      funext i j
      fin_cases i
      · exact congrFun
          (congrArg (fun u ↦ u.2.1) (congrFun hef 1)) j
      · exact congrFun
          (congrArg (fun u ↦ u.2.1) (congrFun hef 2)) j
      · exact congrFun
          (congrArg (fun u ↦ u.2.1) (congrFun hef 0)) j
    · apply Subtype.ext
      apply Subtype.ext
      funext i j
      fin_cases i
      · exact congrFun
          (congrArg (fun u ↦ u.2.2) (congrFun hef 2)) j
      · exact congrFun
          (congrArg (fun u ↦ u.2.2) (congrFun hef 0)) j
      · exact congrFun
          (congrArg (fun u ↦ u.2.2) (congrFun hef 1)) j

/- Inlined accepted legacy proof: mme_stothers_phi134_cyclic_pair_retention_card_le. -/
open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

theorem mme_stothers_phi134_cyclic_pair_retention_card_le
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
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
    exact hne (mme_stothers_phi134_cyclic_mode_word_tuple_injective h)
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
    simp [H, cyclicAffineHash, weights, shift, L0]
  have hH2 (q : (I → ZMod p) × ZMod p) :
      H q 2 e = shift q.1 + q.2 + L2 q.1 := by
    rw [show H q 2 e =
        shift q.1 + 6 * ((6 : ZMod p)⁻¹ * q.2) + L2 q.1 by
      simp [H, cyclicAffineHash, weights, shift, L2]]
    rw [← mul_assoc, mul_inv_cancel₀ h6, one_mul]
  have hvertex (q : (I → ZMod p) × ZMod p)
      (a b : CyclicExactEdge N alpha beta gamma delta) (i : Fin 3)
      (hab : cyclicModeWord a i = cyclicModeWord b i) :
      H q i a = H q i b := by
    simp [H, cyclicAffineHash, hab]
  have hcsum (w : I → ZMod p) :
      (∑ x : I, c x * w x) =
        ∑ r : Fin 3, ∑ j : Fin (2 * N),
          (cyclicHashModeCode p N k (cyclicModeWord e k) r j -
            cyclicHashModeCode p N k (cyclicModeWord f k) r j) *
              w (Sum.inl (r, j)) := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [I, c]
  have hdifference (q : (I → ZMod p) × ZMod p)
      (i : Fin 3) (a b : CyclicExactEdge N alpha beta gamma delta) :
      H q i a - H q i b =
        ∑ r : Fin 3, ∑ j : Fin (2 * N),
          (cyclicHashModeCode p N i (cyclicModeWord a i) r j -
            cyclicHashModeCode p N i (cyclicModeWord b i) r j) *
              weights q.1 r j := by
    simp only [H, cyclicAffineHash]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    ring
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
      rw [← hdifference q k e f]
      exact sub_eq_zero.mpr hkhash
    · have he20 : H q 2 e = H q 0 e :=
        (he 2).trans (he 0).symm
      rw [hH2 q, hH0 q] at he20
      dsimp only [offset]
      linear_combination he20
  exact mme_ZMod_prime_affine_joint_fintype_card_le
    hcard c (Sum.inl (r, j)) hc offset joint hnormal

/- Inlined accepted legacy proof: mme_stothers_phi134_hash_degree_bound. -/
open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

noncomputable section

theorem mme_stothers_phi134_hash_degree_bound
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N)
    [DecidableEq (CyclicModeWord N)] :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    ∀ i : Fin 3,
      ∀ e ∈ edgeFinset N alpha beta gamma delta,
        ((edgeFinset N alpha beta gamma delta).filter
          (fun f ↦ cyclicModeWord f i = cyclicModeWord e i)).card ≤
            D 0 * (D 1 * D 2) := by
  classical
  dsimp only
  intro i e _he
  letI := cyclicExactEdgeFintype N alpha beta gamma delta
  have h := mme_stothers_phi134_cyclic_mode_fiber_card
    N alpha beta gamma delta hsum e i
  rw [Nat.card_eq_fintype_card] at h
  change ((Finset.univ : Finset
      (CyclicExactEdge N alpha beta gamma delta)).filter
        (fun f ↦ cyclicModeWord f i = cyclicModeWord e i)).card ≤ _
  rw [← Fintype.card_subtype]
  exact h.le

end

/- Inlined accepted legacy proof: mme_stothers_phi134_marginals_force_exact_profile. -/
open BigOperators

namespace MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

private theorem inline_marginals_force_exact_profile_pattern_injective : Function.Injective pattern := by
  intro r s h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  fin_cases r <;> fin_cases s <;>
    simp [pattern, MME.cwSquareBlockType] at h0 h1 h2 ⊢

private noncomputable def coordinateClass
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) : Fin 8 :=
  Classical.choose (hx j)

private theorem inline_marginals_force_exact_profile_coordinateClass_spec
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) :
    addressType x j = pattern (coordinateClass x hx j) :=
  Classical.choose_spec (hx j)

private theorem inline_marginals_force_exact_profile_projectedFiberCard
    {N : ℕ} (w : Fin (2 * N) → Fin 8) (i : Fin 3) (s : Fin 5) :
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ pattern (w j) i = s)).card =
      ∑ r : {r : Fin 8 // pattern r i = s},
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ w j = r.1)).card := by
  classical
  let e :
      {j : Fin (2 * N) // pattern (w j) i = s} ≃
        Sigma fun r : {r : Fin 8 // pattern r i = s} ↦
          {j : Fin (2 * N) // w j = r.1} := {
    toFun j := ⟨⟨w j.1, j.2⟩, ⟨j.1, rfl⟩⟩
    invFun x := ⟨x.2.1, by
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
  intro r _hr
  rw [← Fintype.card_subtype]

private theorem inline_marginals_force_exact_profile_sum_ite_eq_sum_subtype
    {beta iota M : Type*} [Fintype beta] [DecidableEq iota]
    [AddCommMonoid M] (q : beta → iota) (i : iota) (f : beta → M) :
    (∑ b : beta, if q b = i then f b else 0) =
      ∑ b : {b : beta // q b = i}, f b.1 := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    ((Finset.univ : Finset beta).filter (fun b ↦ q b = i))
    (fun b ↦ by simp) f

private theorem inline_marginals_force_exact_profile_label_counts_of_marginals
    (N alpha beta gamma delta : ℕ)
    (w : Fin (2 * N) → Fin 8)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ pattern (w j) i = s)).card =
          marginalMultiplicity N alpha beta gamma delta i s) :
    ∀ r : Fin 8,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ w j = r)).card =
          profileMultiplicity alpha beta gamma delta r := by
  let k : Fin 8 → ℕ := fun r ↦
    ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ w j = r)).card
  have h24 := hmarginal 2 4
  have h20 := hmarginal 2 0
  have h10 := hmarginal 1 0
  have h13 := hmarginal 1 3
  have h23 := hmarginal 2 3
  have h21 := hmarginal 2 1
  have h11 := hmarginal 1 1
  have h12 := hmarginal 1 2
  rw [inline_marginals_force_exact_profile_projectedFiberCard, ← inline_marginals_force_exact_profile_sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 2) (4 : Fin 5) k] at h24
  rw [inline_marginals_force_exact_profile_projectedFiberCard, ← inline_marginals_force_exact_profile_sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 2) (0 : Fin 5) k] at h20
  rw [inline_marginals_force_exact_profile_projectedFiberCard, ← inline_marginals_force_exact_profile_sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 1) (0 : Fin 5) k] at h10
  rw [inline_marginals_force_exact_profile_projectedFiberCard, ← inline_marginals_force_exact_profile_sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 1) (3 : Fin 5) k] at h13
  rw [inline_marginals_force_exact_profile_projectedFiberCard, ← inline_marginals_force_exact_profile_sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 2) (3 : Fin 5) k] at h23
  rw [inline_marginals_force_exact_profile_projectedFiberCard, ← inline_marginals_force_exact_profile_sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 2) (1 : Fin 5) k] at h21
  rw [inline_marginals_force_exact_profile_projectedFiberCard, ← inline_marginals_force_exact_profile_sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 1) (1 : Fin 5) k] at h11
  rw [inline_marginals_force_exact_profile_projectedFiberCard, ← inline_marginals_force_exact_profile_sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 1) (2 : Fin 5) k] at h12
  change (∑ r : Fin 8, if pattern r 2 = 4 then k r else 0) = alpha at h24
  change (∑ r : Fin 8, if pattern r 2 = 0 then k r else 0) = alpha at h20
  change (∑ r : Fin 8, if pattern r 1 = 0 then k r else 0) =
    alpha + delta at h10
  change (∑ r : Fin 8, if pattern r 1 = 3 then k r else 0) =
    alpha + delta at h13
  change (∑ r : Fin 8, if pattern r 2 = 3 then k r else 0) =
    beta + delta at h23
  change (∑ r : Fin 8, if pattern r 2 = 1 then k r else 0) =
    beta + delta at h21
  change (∑ r : Fin 8, if pattern r 1 = 1 then k r else 0) =
    beta + gamma at h11
  change (∑ r : Fin 8, if pattern r 1 = 2 then k r else 0) =
    beta + gamma at h12
  simp [pattern, MME.cwSquareBlockType, Fin.sum_univ_succ] at h24 h20 h10 h13 h23 h21 h11 h12
  intro r
  change k r = profileMultiplicity alpha beta gamma delta r
  fin_cases r <;> simp [profileMultiplicity] <;> omega

end MME.StothersFourth.Phi134

theorem mme_stothers_phi134_marginals_force_exact_profile
    (N alpha beta gamma delta : ℕ)
    (x : MME.StothersFourth.Phi134.MarginalAddress
      N alpha beta gamma delta) :
    ∀ r : Fin 8,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦
          MME.StothersFourth.Phi134.addressType x.1 j =
            MME.StothersFourth.Phi134.pattern r)).card =
        MME.StothersFourth.Phi134.profileMultiplicity
          alpha beta gamma delta r := by
  classical
  let w : Fin (2 * N) → Fin 8 :=
    MME.StothersFourth.Phi134.coordinateClass x.1 x.2.1
  have htype (j : Fin (2 * N)) :
      MME.StothersFourth.Phi134.addressType x.1 j =
        MME.StothersFourth.Phi134.pattern (w j) := by
    exact MME.StothersFourth.Phi134.inline_marginals_force_exact_profile_coordinateClass_spec x.1 x.2.1 j
  have hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ MME.StothersFourth.Phi134.pattern (w j) i = s)).card =
          MME.StothersFourth.Phi134.marginalMultiplicity
            N alpha beta gamma delta i s := by
    intro i s
    rw [← x.2.2 i s]
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hij := congrFun (htype j) i
    change x.1 i j = MME.StothersFourth.Phi134.pattern (w j) i at hij
    exact ⟨fun h ↦ hij.trans h, fun h ↦ hij.symm.trans h⟩
  have hcounts :=
    MME.StothersFourth.Phi134.inline_marginals_force_exact_profile_label_counts_of_marginals
      N alpha beta gamma delta w hmarginal
  intro r
  rw [← hcounts r]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    apply MME.StothersFourth.Phi134.inline_marginals_force_exact_profile_pattern_injective
    exact (htype j).symm.trans h
  · intro h
    exact (htype j).trans (congrArg MME.StothersFourth.Phi134.pattern h)

/- Inlined accepted legacy proof: mme_stothers_phi134_cyclic_supported_mix_closure. -/
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

theorem mme_stothers_phi134_cyclic_supported_mix_closure
    {N alpha beta gamma delta : ℕ}
    (x y z : CyclicExactEdge N alpha beta gamma delta)
    (hsupport : CyclicCoordinatewiseSupported x y z) :
    ∃ e : CyclicExactEdge N alpha beta gamma delta,
      cyclicModeWord e 0 = cyclicModeWord x 0 ∧
      cyclicModeWord e 1 = cyclicModeWord y 1 ∧
      cyclicModeWord e 2 = cyclicModeWord z 2 := by
  let e₀m := mixedMarginalAddress x.1.1 y.1.1 z.1.1 hsupport.1
  let e₁m := mixedMarginalAddress
    y.2.1.1 z.2.1.1 x.2.1.1 hsupport.2.1
  let e₂m := mixedMarginalAddress
    z.2.2.1 x.2.2.1 y.2.2.1 hsupport.2.2
  let e₀ : ExactProfileAddress N alpha beta gamma delta :=
    ⟨e₀m, mme_stothers_phi134_marginals_force_exact_profile
      N alpha beta gamma delta e₀m⟩
  let e₁ : ExactProfileAddress N alpha beta gamma delta :=
    ⟨e₁m, mme_stothers_phi134_marginals_force_exact_profile
      N alpha beta gamma delta e₁m⟩
  let e₂ : ExactProfileAddress N alpha beta gamma delta :=
    ⟨e₂m, mme_stothers_phi134_marginals_force_exact_profile
      N alpha beta gamma delta e₂m⟩
  exact ⟨(e₀, (e₁, e₂)), rfl, rfl, rfl⟩

/- Inlined accepted legacy proof: mme_stothers_phi134_retained_exact_closure. -/
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

theorem mme_stothers_phi134_retained_exact_closure
    {p N alpha beta gamma delta : ℕ}
    (S : Finset (ZMod p))
    (hSfree : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a + b = 2 * c → a = c ∧ c = b)
    (q : HashState p N) :
    ∀ x ∈ retainedEdges p N alpha beta gamma delta S q,
      ∀ y ∈ retainedEdges p N alpha beta gamma delta S q,
        ∀ z ∈ retainedEdges p N alpha beta gamma delta S q,
          CyclicCoordinatewiseSupported x y z →
            ∃ e ∈ retainedEdges p N alpha beta gamma delta S q,
              cyclicModeWord e 0 = cyclicModeWord x 0 ∧
              cyclicModeWord e 1 = cyclicModeWord y 1 ∧
              cyclicModeWord e 2 = cyclicModeWord z 2 := by
  classical
  intro x hx y hy z hz hsupp
  have hxRetained : Retained p N alpha beta gamma delta S q x := by
    have hx' : x ∈ edgeFinset N alpha beta gamma delta ∧
        Retained p N alpha beta gamma delta S q x := by
      simpa only [retainedEdges, Finset.mem_filter] using hx
    exact hx'.2
  have hyRetained : Retained p N alpha beta gamma delta S q y := by
    have hy' : y ∈ edgeFinset N alpha beta gamma delta ∧
        Retained p N alpha beta gamma delta S q y := by
      simpa only [retainedEdges, Finset.mem_filter] using hy
    exact hy'.2
  have hzRetained : Retained p N alpha beta gamma delta S q z := by
    have hz' : z ∈ edgeFinset N alpha beta gamma delta ∧
        Retained p N alpha beta gamma delta S q z := by
      simpa only [retainedEdges, Finset.mem_filter] using hz
    exact hz'.2
  obtain ⟨sx, hsx, hxs⟩ := hxRetained
  obtain ⟨sy, hsy, hys⟩ := hyRetained
  obtain ⟨sz, hsz, hzs⟩ := hzRetained
  have hap :
      stateHash p N alpha beta gamma delta q 0 x +
          stateHash p N alpha beta gamma delta q 1 y =
        2 * stateHash p N alpha beta gamma delta q 2 z := by
    simpa only [stateHash] using
      (mme_stothers_phi134_cyclic_affine_hash_AP
        (stateWeights q) (stateShift q) ((6 : ZMod p)⁻¹ * q.2)
        x y z hsupp)
  have hlabels : sx = sz ∧ sz = sy := by
    apply hSfree sx hsx sy hsy sz hsz
    simpa only [hxs 0, hys 1, hzs 2] using hap
  obtain ⟨e, he0, he1, he2⟩ :=
    mme_stothers_phi134_cyclic_supported_mix_closure x y z hsupp
  have hvertex (i : Fin 3)
      (a b : CyclicExactEdge N alpha beta gamma delta)
      (hab : cyclicModeWord a i = cyclicModeWord b i) :
      stateHash p N alpha beta gamma delta q i a =
        stateHash p N alpha beta gamma delta q i b := by
    simp [stateHash, cyclicAffineHash, hab]
  refine ⟨e, ?_, he0, he1, he2⟩
  simp only [retainedEdges, Finset.mem_filter]
  constructor
  · simp [edgeFinset]
  · refine ⟨sx, hsx, ?_⟩
    intro i
    fin_cases i
    · exact (hvertex 0 e x he0).trans (hxs 0)
    · exact (hvertex 1 e y he1).trans
        ((hys 1).trans (hlabels.2.symm.trans hlabels.1.symm))
    · exact (hvertex 2 e z he2).trans
        ((hzs 2).trans hlabels.1.symm)

/- Inlined accepted legacy proof: mme_stothers_phi134_finite_isolation_of_hash_margin. -/
open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

/-- The source-specific finite Type-2 isolation adapter for `Phi134`.
The only remaining quantitative input is the collision margin. -/
theorem mme_stothers_phi134_finite_isolation_of_hash_margin
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hsum : alpha + beta + gamma + delta = N)
    (S : Finset (ZMod p))
    (hSfree : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a + b = 2 * c → a = c ∧ c = b)
    (loss : ℝ) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let State := (I → ZMod p) × ZMod p
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : State) (i : Fin 3)
        (e : CyclicExactEdge N alpha beta gamma delta) ↦
      cyclicAffineHash p N alpha beta gamma delta
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i e
    let retain := fun (q : State)
        (e : CyclicExactEdge N alpha beta gamma delta) ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i e = s
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    let Dstar := D 0 * (D 1 * D 2)
    let V := ∏ i : Fin 3,
      Nat.multinomial Finset.univ
        (marginalMultiplicity N alpha beta gamma delta i)
    ((p ^ 2 : ℕ) : ℝ) * loss +
          3 * (Dstar : ℝ) * (Dstar : ℝ) ≤
        (Dstar : ℝ) * (S.card : ℝ) →
      ∃ q : State,
        ∃ kept : Finset (CyclicExactEdge N alpha beta gamma delta),
          kept ⊆ (edgeFinset N alpha beta gamma delta).filter (retain q) ∧
          (∀ i : Fin 3,
            Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
          (∀ x y z : kept,
            CyclicCoordinatewiseSupported x.1 y.1 z.1 →
              x = y ∧ y = z) ∧
          (V : ℝ) * loss ≤ (kept.card : ℝ) := by
  classical
  dsimp only
  let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
  let State := (I → ZMod p) × ZMod p
  let weights := fun w : I → ZMod p ↦
    fun r j ↦ w (Sum.inl (r, j))
  let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
  let H := fun (q : State) (i : Fin 3)
      (e : CyclicExactEdge N alpha beta gamma delta) ↦
    cyclicAffineHash p N alpha beta gamma delta
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i e
  let retain := fun (q : State)
      (e : CyclicExactEdge N alpha beta gamma delta) ↦
    ∃ s ∈ S, ∀ i : Fin 3, H q i e = s
  let D : Fin 3 → ℕ := fun t ↦
    ∏ s : Fin 5,
      (marginalMultiplicity N alpha beta gamma delta t s).factorial /
        ∏ r : {r : Fin 8 // pattern r t = s},
          (profileMultiplicity alpha beta gamma delta r.1).factorial
  let Dstar : ℕ := D 0 * (D 1 * D 2)
  let V : ℕ := ∏ i : Fin 3,
    Nat.multinomial Finset.univ
      (marginalMultiplicity N alpha beta gamma delta i)
  intro hmargin
  change ((p ^ 2 : ℕ) : ℝ) * loss +
      3 * (Dstar : ℝ) * (Dstar : ℝ) ≤
        (Dstar : ℝ) * (S.card : ℝ) at hmargin
  change ∃ q : State,
    ∃ kept : Finset (CyclicExactEdge N alpha beta gamma delta),
      kept ⊆ (edgeFinset N alpha beta gamma delta).filter (retain q) ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
      (∀ x y z : kept,
        CyclicCoordinatewiseSupported x.1 y.1 z.1 →
          x = y ∧ y = z) ∧
      (V : ℝ) * loss ≤ (kept.card : ℝ)
  letI : Nonempty State := ⟨((fun _ ↦ 0), 0)⟩
  have hstate : Fintype.card State = p ^ 2 * p ^ (6 * N) := by
    dsimp only [State, I]
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_unit, ZMod.card]
    rw [show 3 * (2 * N) + 1 = 6 * N + 1 by omega]
    ring
  have hedgeCardNat :
      (edgeFinset N alpha beta gamma delta).card =
        (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 := by
    letI := exactProfileAddressFintype N alpha beta gamma delta
    letI := cyclicExactEdgeFintype N alpha beta gamma delta
    change Fintype.card
        (ExactProfileAddress N alpha beta gamma delta ×
          (ExactProfileAddress N alpha beta gamma delta ×
            ExactProfileAddress N alpha beta gamma delta)) = _
    rw [Nat.card_eq_fintype_card]
    simp only [Fintype.card_prod]
    ring
  have hcapacity := mme_stothers_phi134_capacity_identity
    N alpha beta gamma delta hsum
  change V * Dstar =
    (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 at hcapacity
  have htargetCard :
      ((edgeFinset N alpha beta gamma delta).card : ℝ) =
        (V : ℝ) * (Dstar : ℝ) := by
    exact_mod_cast hedgeCardNat.trans hcapacity.symm
  have hdegree : ∀ i : Fin 3,
      ∀ e ∈ edgeFinset N alpha beta gamma delta,
        ((edgeFinset N alpha beta gamma delta).filter
          (fun f ↦ cyclicModeWord f i = cyclicModeWord e i)).card ≤
            Dstar := by
    simpa only [D, Dstar] using
      (mme_stothers_phi134_hash_degree_bound
        N alpha beta gamma delta hsum)
  have hedge : ∀ e ∈ edgeFinset N alpha beta gamma delta,
      ((Finset.univ : Finset State).filter
        (fun q ↦ retain q e)).card =
          S.card * p ^ (6 * N) := by
    intro e _he
    simpa only [State, retain, H, I, weights, shift] using
      (mme_stothers_phi134_cyclic_edge_retention_card hp e S)
  have hpair : ∀ ef ∈
      ((edgeFinset N alpha beta gamma delta ×ˢ
        edgeFinset N alpha beta gamma delta).filter (fun ef ↦
          ef.1 ≠ ef.2 ∧ ∃ i : Fin 3,
            cyclicModeWord ef.1 i = cyclicModeWord ef.2 i)),
      ((Finset.univ : Finset State).filter (fun q ↦
        retain q ef.1 ∧ retain q ef.2)).card ≤
        p ^ (6 * N) := by
    intro ef hef
    simp only [Finset.mem_filter, Finset.mem_product] at hef
    obtain ⟨hne, i, hi⟩ := hef.2
    simpa only [State, retain, H, I, weights, shift] using
      (mme_stothers_phi134_cyclic_pair_retention_card_le
        hp ef.1 ef.2 S hne i hi)
  have hclosure : ∀ q : State,
      ∀ x ∈ (edgeFinset N alpha beta gamma delta).filter
        (retain q),
      ∀ y ∈ (edgeFinset N alpha beta gamma delta).filter
        (retain q),
      ∀ z ∈ (edgeFinset N alpha beta gamma delta).filter
        (retain q),
        CyclicCoordinatewiseSupported x y z →
          ∃ e ∈ (edgeFinset N alpha beta gamma delta).filter
            (retain q),
            cyclicModeWord e 0 = cyclicModeWord x 0 ∧
            cyclicModeWord e 1 = cyclicModeWord y 1 ∧
            cyclicModeWord e 2 = cyclicModeWord z 2 := by
    intro q x hx y hy z hz hsupp
    have hweights :
        MME.StothersFourth.Phi134.stateWeights q = weights q.1 := rfl
    have hx' : x ∈ retainedEdges p N alpha beta gamma delta S q := by
      simpa only [retainedEdges, Finset.mem_filter, retain, H, State, I,
        Retained, stateHash, hweights, stateShift, weights, shift] using hx
    have hy' : y ∈ retainedEdges p N alpha beta gamma delta S q := by
      simpa only [retainedEdges, Finset.mem_filter, retain, H, State, I,
        Retained, stateHash, hweights, stateShift, weights, shift] using hy
    have hz' : z ∈ retainedEdges p N alpha beta gamma delta S q := by
      simpa only [retainedEdges, Finset.mem_filter, retain, H, State, I,
        Retained, stateHash, hweights, stateShift, weights, shift] using hz
    obtain ⟨e, he, he0, he1, he2⟩ :=
      mme_stothers_phi134_retained_exact_closure
        S hSfree q x hx' y hy' z hz' hsupp
    exact ⟨e, by
      simpa only [retainedEdges, Finset.mem_filter, retain, H, State, I,
        Retained, stateHash, hweights, stateShift, weights, shift] using he,
      he0, he1, he2⟩
  exact
    (mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers
      (Vertex := fun _ ↦ CyclicModeWord N)
      (fun i e ↦ cyclicModeWord e i)
      CyclicCoordinatewiseSupported
      (edgeFinset N alpha beta gamma delta)
      (edgeFinset N alpha beta gamma delta)
      retain
      (p ^ 2) S.card (p ^ (6 * N)) Dstar Dstar
      (V : ℝ) loss (Nat.cast_nonneg V) hstate htargetCard hdegree
      hedge hpair Finset.Subset.rfl hclosure hmargin)

/- Inlined accepted legacy proof: mme_stothers_phi134_entropy_rate_identity. -/
open MME Real

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

/-- The entropy of the three marginal word classes for the symmetric
`phi_134` profile, normalized by the even tensor-power length `2N`. -/
noncomputable def phi134MarginalEntropy
    (sigma a c : ℝ) : ℝ :=
  (3 - c) * Real.log 2 +
    Real.negMulLog sigma + Real.negMulLog (1 - sigma) +
    Real.negMulLog a + Real.negMulLog c +
    Real.negMulLog (1 - a - c)

/-- The marginal entropy plus the eight component values is exactly the
profile-parametric rate printed in Davie--Stothers Lemma 5.1(iii).  The proof
also covers the allowed boundary `1-a-c=0`, using the `0^0=1` convention of
real powers. -/
theorem phi134_entropy_rate_identity_aux
    (sigma a c L E H : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H) :
    phi134MarginalEntropy sigma a c +
          sigma * Real.log L +
          ((1 - sigma) + (1 - a - c)) * Real.log E +
          c * Real.log H =
      Real.log
        (8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))) := by
  have hsigma : 0 < sigma := lt_of_lt_of_le hc hcs
  have honesigma : 0 < 1 - sigma := by linarith
  have ht : 0 ≤ 1 - a - c := by linarith
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  by_cases ht0 : 1 - a - c = 0
  · unfold phi134MarginalEntropy
    rw [ht0]
    simp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by positivity : 0 < L / sigma),
      Real.log_rpow (by positivity : 0 < E / (1 - sigma)),
      Real.log_rpow (by positivity : 0 < a⁻¹),
      Real.log_rpow (by positivity : 0 < (H / 2) / c),
      Real.log_div hL.ne' hsigma.ne',
      Real.log_div hE.ne' honesigma.ne',
      Real.log_inv a,
      Real.log_div (div_ne_zero hH.ne' h2) hc.ne',
      Real.log_div hH.ne' h2, hlog8]
    unfold Real.negMulLog
    norm_num
    ring

  · have htpos : 0 < 1 - a - c := lt_of_le_of_ne ht (Ne.symm ht0)
    unfold phi134MarginalEntropy
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by positivity : 0 < L / sigma),
      Real.log_rpow (by positivity : 0 < E / (1 - sigma)),
      Real.log_rpow (by positivity : 0 < 1 / a),
      Real.log_rpow (by positivity : 0 < (H / 2) / c),
      Real.log_rpow (by positivity : 0 < E / (1 - a - c)),
      Real.log_div hL.ne' hsigma.ne',
      Real.log_div hE.ne' honesigma.ne',
      Real.log_div one_ne_zero ha.ne',
      Real.log_div (div_ne_zero hH.ne' h2) hc.ne',
      Real.log_div hH.ne' h2,
      Real.log_div hE.ne' htpos.ne', Real.log_one, hlog8]
    unfold Real.negMulLog
    norm_num
    ring

theorem mme_stothers_phi134_entropy_rate_identity
    (sigma a c L E H : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H) :
    ((3 - c) * Real.log 2 +
        Real.negMulLog sigma + Real.negMulLog (1 - sigma) +
        Real.negMulLog a + Real.negMulLog c +
        Real.negMulLog (1 - a - c)) +
          sigma * Real.log L +
          ((1 - sigma) + (1 - a - c)) * Real.log E +
          c * Real.log H =
      Real.log
        (8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))) := by
  change phi134MarginalEntropy sigma a c +
          sigma * Real.log L +
          ((1 - sigma) + (1 - a - c)) * Real.log E +
          c * Real.log H = _
  exact phi134_entropy_rate_identity_aux
    sigma a c L E H ha hc hcs hsa hL hE hH

/- Inlined accepted legacy proof: mme_stothers_phi134_analytic_profile_surplus. -/
open MME Real BigOperators Filter

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace MME.StothersFourth.Phi134AnalyticSurplus

private theorem inline_analytic_profile_surplus_scaled_log_limit (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ Real.log (s * n + 1) / (2 * n))
      atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ ↦ s * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop hs)
  have hl := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ht
  have hr : Tendsto (fun n : ℕ ↦ (s * n + 1) / (2 * n))
      atTop (nhds (s / 2)) := by
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

private theorem inline_analytic_profile_surplus_scaled_sqrt_limit (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ Real.sqrt (s * n + 1) / (2 * n))
      atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ ↦ s * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop hs)
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp ht)
  have hr : Tendsto (fun n : ℕ ↦ (s * n + 1) / (2 * n))
      atTop (nhds (s / 2)) := by
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

private theorem inline_analytic_profile_surplus_penalty_limit :
    Tendsto (fun n : ℕ ↦
      (15 * Real.log (6 * ((2 * n + 1 : ℕ) : ℝ)) +
        4000 * Real.sqrt ((12 * n + 1 : ℕ) : ℝ)) / (2 * n))
      atTop (nhds 0) := by
  have hl := inline_analytic_profile_surplus_scaled_log_limit 2 (by norm_num)
  have hs := inline_analytic_profile_surplus_scaled_sqrt_limit 12 (by norm_num)
  have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh :=
    ((((hi.const_mul (Real.log 6)).div_const 2).add hl).const_mul 15 |>.add
      (hs.const_mul 4000))
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hp : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hp]
    ring

private noncomputable def entropyAt
    (A B C : ℕ → ℕ) (n : ℕ) : ℝ :=
  let an := (A n : ℝ) / n
  let cn := (C n : ℝ) / n
  let sn := ((B n : ℝ) + C n) / n
  (3 - cn) * Real.log 2 +
    Real.negMulLog sn + Real.negMulLog (1 - sn) +
    Real.negMulLog an + Real.negMulLog cn +
    Real.negMulLog (1 - an - cn)

end MME.StothersFourth.Phi134AnalyticSurplus

open MME.StothersFourth.Phi134AnalyticSurplus

/-- Abstract analytic heart of the Phi134 profile extraction.  Any exact
finite counting layer satisfying the displayed capacity lower bound can be
combined with convergent integral profile sequences to produce a strict
finite surplus. -/
theorem mme_stothers_phi134_analytic_profile_surplus
    (sigma a c L E H V : ℝ)
    (A B C D degree targetCard : ℕ → ℕ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H)
    (hV : 0 < V)
    (hVlt :
      V <
        8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c)))
    (hsum : ∀ n, A n + B n + C n + D n = n)
    (hA : Tendsto (fun n : ℕ ↦ (A n : ℝ) / n) atTop (nhds a))
    (hB : Tendsto (fun n : ℕ ↦ (B n : ℝ) / n) atTop
      (nhds (sigma - c)))
    (hC : Tendsto (fun n : ℕ ↦ (C n : ℝ) / n) atTop (nhds c))
    (hD : Tendsto (fun n : ℕ ↦ (D n : ℝ) / n) atTop
      (nhds (1 - sigma - a)))
    (hdegree : ∀ n, 0 < n → 0 < degree n)
    (hcapacity : ∀ n : ℕ, 0 < n →
      Real.exp ((2 * n : ℝ) *
        (let an := (A n : ℝ) / n
         let cn := (C n : ℝ) / n
         let sn := ((B n : ℝ) + C n) / n
         (3 - cn) * Real.log 2 +
           Real.negMulLog sn + Real.negMulLog (1 - sn) +
           Real.negMulLog an + Real.negMulLog cn +
           Real.negMulLog (1 - an - cn))) ≤
        (6 * ((2 * n + 1 : ℕ) : ℝ)) ^ (15 : ℕ) *
          ((targetCard n : ℝ) ^ (3 : ℕ) / (degree n : ℝ))) :
    ∃ n : ℕ, 0 < n ∧ A n + B n + C n + D n = n ∧
      V ^ (2 * n) * (degree n : ℝ) *
          Real.exp (4000 * Real.sqrt ((12 * n + 1 : ℕ) : ℝ)) <
        (targetCard n : ℝ) ^ (3 : ℕ) *
          (L ^ (2 * B n + 2 * C n) *
            E ^ (2 * A n + 2 * B n + 4 * D n) *
            H ^ (2 * C n)) := by
  let an := fun n : ℕ ↦ (A n : ℝ) / n
  let bn := fun n : ℕ ↦ (B n : ℝ) / n
  let cn := fun n : ℕ ↦ (C n : ℝ) / n
  let dn := fun n : ℕ ↦ (D n : ℝ) / n
  let sn := fun n : ℕ ↦ ((B n : ℝ) + C n) / n
  have hsn0 := hB.add hC
  have hsn : Tendsto sn atTop (nhds sigma) := by
    have hh : Tendsto sn atTop (nhds ((sigma - c) + c)) := by
      apply hsn0.congr'
      exact Filter.Eventually.of_forall (fun n ↦ by
        dsimp only [sn]
        rw [add_div])
    have hlimit : (sigma - c) + c = sigma := by ring
    rw [hlimit] at hh
    exact hh
  have hneg {f : ℕ → ℝ} {x : ℝ}
      (h : Tendsto f atTop (nhds x)) :
      Tendsto (fun n ↦ Real.negMulLog (f n)) atTop
        (nhds (Real.negMulLog x)) :=
    Real.continuous_negMulLog.continuousAt.tendsto.comp h
  have hthree : Tendsto (fun n ↦ (3 : ℝ) - cn n) atTop
      (nhds (3 - c)) := tendsto_const_nhds.sub hC
  have hones : Tendsto (fun n ↦ (1 : ℝ) - sn n) atTop
      (nhds (1 - sigma)) := tendsto_const_nhds.sub hsn
  have honeac : Tendsto (fun n ↦ (1 : ℝ) - an n - cn n) atTop
      (nhds (1 - a - c)) :=
    (tendsto_const_nhds.sub hA).sub hC
  have hent : Tendsto (fun n ↦ entropyAt A B C n) atTop
      (nhds
        ((3 - c) * Real.log 2 +
          Real.negMulLog sigma + Real.negMulLog (1 - sigma) +
          Real.negMulLog a + Real.negMulLog c +
          Real.negMulLog (1 - a - c))) := by
    have hh :=
      (((((hthree.mul_const (Real.log 2)).add (hneg hsn)).add
        (hneg hones)).add (hneg hA)).add (hneg hC)).add (hneg honeac)
    change Tendsto (fun n ↦
      (3 - cn n) * Real.log 2 +
        Real.negMulLog (sn n) + Real.negMulLog (1 - sn n) +
        Real.negMulLog (an n) + Real.negMulLog (cn n) +
        Real.negMulLog (1 - an n - cn n)) atTop _
    exact hh
  have hecoef0 := ((hA.add hB).add (hD.const_mul 2))
  have hecoef : Tendsto
      (fun n ↦ an n + bn n + 2 * dn n) atTop
      (nhds ((1 - sigma) + (1 - a - c))) := by
    change Tendsto (fun n ↦ an n + bn n + 2 * dn n) atTop _ at hecoef0
    have hlimit : a + (sigma - c) + 2 * (1 - sigma - a) =
        (1 - sigma) + (1 - a - c) := by ring
    rw [hlimit] at hecoef0
    exact hecoef0
  let rate := fun n : ℕ ↦ entropyAt A B C n +
    sn n * Real.log L +
    (an n + bn n + 2 * dn n) * Real.log E +
    cn n * Real.log H
  have hrate0 :=
    (((hent.add (hsn.mul_const (Real.log L))).add
      (hecoef.mul_const (Real.log E))).add
      (hC.mul_const (Real.log H)))
  have hrate : Tendsto rate atTop
      (nhds (Real.log
        (8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))))) := by
    rw [← mme_stothers_phi134_entropy_rate_identity
      sigma a c L E H ha hc hcs hsa hL hE hH]
    change Tendsto (fun n ↦ entropyAt A B C n +
      sn n * Real.log L +
      (an n + bn n + 2 * dn n) * Real.log E +
      cn n * Real.log H) atTop _
    exact hrate0
  have hlim := hrate.sub
    MME.StothersFourth.Phi134AnalyticSurplus.inline_analytic_profile_surplus_penalty_limit
  have hlog := Real.log_lt_log hV hVlt
  have hevent := hlim.eventually
    (eventually_gt_nhds (by simpa only [sub_zero] using hlog))
  obtain ⟨N, hN, hgap⟩ := ((eventually_gt_atTop 0).and hevent).exists
  let P : ℝ := 6 * ((2 * N + 1 : ℕ) : ℝ)
  let Q : ℝ := ((12 * N + 1 : ℕ) : ℝ)
  let Deg : ℝ := (degree N : ℝ)
  let T : ℝ := (targetCard N : ℝ) ^ (3 : ℕ)
  let J : ℝ :=
    L ^ (2 * B N + 2 * C N) *
      E ^ (2 * A N + 2 * B N + 4 * D N) *
      H ^ (2 * C N)
  have hDeg : 0 < Deg := by
    dsimp only [Deg]
    exact_mod_cast hdegree N hN
  have hP : 0 < P := by dsimp only [P]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hcap := hcapacity N hN
  change Real.exp ((2 * N : ℝ) * entropyAt A B C N) ≤
    P ^ (15 : ℕ) * (T / Deg) at hcap
  have hf := mul_le_mul_of_nonneg_right hcap hJ.le
  have hlogJ : Real.log J = (2 * N : ℝ) *
      (sn N * Real.log L +
        (an N + bn N + 2 * dn N) * Real.log E +
        cn N * Real.log H) := by
    dsimp only [J]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    dsimp only [sn, an, bn, cn, dn]
    field_simp
    ring
  have hleft :
      Real.exp ((2 * N : ℝ) * entropyAt A B C N) * J =
        Real.exp ((2 * N : ℝ) * rate N) := by
    rw [← Real.exp_log hJ, ← Real.exp_add, hlogJ]
    congr 1
    dsimp only [rate]
    ring
  rw [hleft] at hf
  have hngap :
      (2 * N : ℝ) * Real.log V + 15 * Real.log P +
          4000 * Real.sqrt Q <
        (2 * N : ℝ) * rate N := by
    have hh := mul_lt_mul_of_pos_left hgap
      (by positivity : (0 : ℝ) < 2 * N)
    change (2 * N : ℝ) * Real.log V <
      (2 * N : ℝ) *
        (rate N -
          (15 * Real.log P + 4000 * Real.sqrt Q) / (2 * N)) at hh
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    field_simp at hh
    nlinarith only [hh]
  have heq :
      (2 * N : ℝ) * Real.log V + 15 * Real.log P +
          4000 * Real.sqrt Q =
        Real.log
          (V ^ (2 * N) * P ^ (15 : ℕ) *
            Real.exp (4000 * Real.sqrt Q)) := by
    conv_rhs =>
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_exp]
    push_cast
    ring
  have hh := (Real.exp_lt_exp.mpr hngap).trans_le hf
  rw [heq, Real.exp_log (by positivity)] at hh
  change
    V ^ (2 * N) * P ^ (15 : ℕ) *
        Real.exp (4000 * Real.sqrt Q) <
      P ^ (15 : ℕ) * (T / Deg) * J at hh
  have hcancel :
      V ^ (2 * N) * Real.exp (4000 * Real.sqrt Q) <
        (T / Deg) * J := by
    have hp15 : 0 < P ^ (15 : ℕ) := by positivity
    nlinarith only [hh, hp15]
  have hcancel' := mul_lt_mul_of_pos_right hcancel hDeg
  refine ⟨N, hN, hsum N, ?_⟩
  change V ^ (2 * N) * Deg * Real.exp (4000 * Real.sqrt Q) < T * J
  field_simp at hcancel'
  nlinarith only [hcancel']

/- Inlined accepted legacy proof: mme_stothers_phi134_capacity_entropy_lower_bound. -/
open MME Real BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option warningAsError true

namespace MME.StothersFourth.Phi134CapacityEntropySubmission

private noncomputable def modeDegree
    (N alpha beta gamma delta : ℕ) (i : Fin 3) : ℕ :=
  ∏ s : Fin 5,
      (marginalMultiplicity N alpha beta gamma delta i s).factorial /
    ∏ r : {r : Fin 8 // pattern r i = s},
      (profileMultiplicity alpha beta gamma delta r.1).factorial

private noncomputable def degree
    (N alpha beta gamma delta : ℕ) : ℕ :=
  modeDegree N alpha beta gamma delta 0 *
    (modeDegree N alpha beta gamma delta 1 *
      modeDegree N alpha beta gamma delta 2)

private theorem inline_capacity_entropy_lower_bound_count_totals
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    ∑ r : Fin 8, profileMultiplicity alpha beta gamma delta r = 2 * N := by
  simp [Fin.sum_univ_succ, profileMultiplicity]
  omega

private theorem inline_capacity_entropy_lower_bound_marginal_totals
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) (i : Fin 3) :
    ∑ s : Fin 5, marginalMultiplicity N alpha beta gamma delta i s =
      2 * N := by
  fin_cases i <;>
    simp [Fin.sum_univ_succ, marginalMultiplicity] <;> omega

private theorem inline_capacity_entropy_lower_bound_multinomial_entropy
    (w : Fin 5 → ℕ) (n : ℕ) (hn : 0 < n)
    (hsum : ∑ i, w i = n) :
    Real.exp ((n : ℝ) *
        ∑ i, Real.negMulLog ((w i : ℝ) / n)) ≤
      (6 * ((n + 1 : ℕ) : ℝ)) ^ 5 *
        (Nat.multinomial Finset.univ w : ℝ) := by
  have h := mme_dwz_multinomial_entropy_polynomial_lower
    w 1 (by omega) (show 0 < ∑ i, w i by omega)
  have hlog : Real.log 2 ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  simp only [hsum, mul_one,
    mme_modern_entropyBits, Fintype.card_fin] at h
  have he (x : ℝ) :
      (n : ℝ) * Real.log 2 * (x / Real.log 2) = n * x := by
    field_simp
  rw [he] at h
  simpa only [Nat.cast_one, one_mul] using h

end MME.StothersFourth.Phi134CapacityEntropySubmission

open MME.StothersFourth.Phi134CapacityEntropySubmission

/-- Finite entropy capacity bound for the Phi134 profile. -/
theorem mme_stothers_phi134_capacity_entropy_lower_bound
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (hsum : alpha + beta + gamma + delta = N) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    let degreeValue := D 0 * (D 1 * D 2)
    Real.exp ((2 * N : ℝ) *
      (let an := (alpha : ℝ) / N
       let cn := (gamma : ℝ) / N
       let sn := ((beta : ℝ) + gamma) / N
       (3 - cn) * Real.log 2 +
         Real.negMulLog sn + Real.negMulLog (1 - sn) +
         Real.negMulLog an + Real.negMulLog cn +
         Real.negMulLog (1 - an - cn))) ≤
      (6 * ((2 * N + 1 : ℕ) : ℝ)) ^ (15 : ℕ) *
        ((Nat.card
          (ExactProfileAddress N alpha beta gamma delta) : ℝ) ^
            (3 : ℕ) /
          (degreeValue : ℝ)) := by
  dsimp only
  have hh (i : Fin 3) := inline_capacity_entropy_lower_bound_multinomial_entropy
    (marginalMultiplicity N alpha beta gamma delta i)
    (2 * N) (by omega)
    (inline_capacity_entropy_lower_bound_marginal_totals N alpha beta gamma delta hsum i)
  have hprod := Finset.prod_le_prod
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦
      (Real.exp_pos _).le)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦ hh i)
  rw [← Real.exp_sum] at hprod
  simp only [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hprod
  have hDnat : 0 < degree N alpha beta gamma delta := by
    have hid := mme_stothers_phi134_capacity_identity
      N alpha beta gamma delta hsum
    change
      (∏ i : Fin 3,
          Nat.multinomial Finset.univ
            (marginalMultiplicity N alpha beta gamma delta i)) *
          degree N alpha beta gamma delta =
        (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 at hid
    have hrows : 0 < ∏ i : Fin 3,
        Nat.multinomial Finset.univ
          (marginalMultiplicity N alpha beta gamma delta i) := by
      apply Finset.prod_pos
      intro i _hi
      exact Nat.multinomial_pos Finset.univ _
    have hcard : 0 < Nat.card
        (ExactProfileAddress N alpha beta gamma delta) := by
      rw [mme_stothers_phi134_exact_profile_card
        N alpha beta gamma delta hsum]
      have hm := Nat.multinomial_pos Finset.univ
        (profileMultiplicity alpha beta gamma delta)
      simpa only [Nat.multinomial,
        inline_capacity_entropy_lower_bound_count_totals N alpha beta gamma delta hsum] using hm
    have hright : 0 <
        (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 :=
      pow_pos hcard _
    have hproduct : 0 <
        (∏ i : Fin 3,
          Nat.multinomial Finset.univ
            (marginalMultiplicity N alpha beta gamma delta i)) *
          degree N alpha beta gamma delta := by
      rw [hid]
      exact hright
    exact (CanonicallyOrderedAdd.mul_pos.mp hproduct).2
  have hD : (degree N alpha beta gamma delta : ℝ) ≠ 0 := by
    exact_mod_cast hDnat.ne'
  have hidNat := mme_stothers_phi134_capacity_identity
    N alpha beta gamma delta hsum
  change
    (∏ i : Fin 3,
        Nat.multinomial Finset.univ
          (marginalMultiplicity N alpha beta gamma delta i)) *
      degree N alpha beta gamma delta =
        (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 at hidNat
  have hid :
      (∏ i : Fin 3,
          (Nat.multinomial Finset.univ
            (marginalMultiplicity N alpha beta gamma delta i) : ℝ)) *
        (degree N alpha beta gamma delta : ℝ) =
      (Nat.card (ExactProfileAddress N alpha beta gamma delta) : ℝ) ^
        (3 : ℕ) := by
    exact_mod_cast hidNat
  have hratio :
      (∏ i : Fin 3,
          (Nat.multinomial Finset.univ
            (marginalMultiplicity N alpha beta gamma delta i) : ℝ)) =
        (Nat.card (ExactProfileAddress N alpha beta gamma delta) : ℝ) ^
            (3 : ℕ) /
          (degree N alpha beta gamma delta : ℝ) :=
    (eq_div_iff hD).mpr hid
  rw [hratio] at hprod
  have hn0 : (N : ℝ) ≠ 0 := by positivity
  have htwoN0 : (2 * (N : ℝ)) ≠ 0 := by positivity
  have hsumR :
      (alpha : ℝ) + beta + gamma + delta = N := by
    exact_mod_cast hsum
  have hhalf : (N : ℝ) / (2 * N) = 1 / 2 := by field_simp
  have henthalf : Real.negMulLog (1 / 2) = Real.log 2 / 2 := by
    norm_num [Real.negMulLog, Real.log_div]
    ring
  have hsplit (x : ℝ) :
      2 * Real.negMulLog (x / 2) =
        Real.negMulLog x + x * Real.log 2 := by
    rw [show x / 2 = x * (1 / 2 : ℝ) by ring,
      Real.negMulLog_mul, henthalf]
    ring
  have habgd :
      ((alpha : ℝ) + delta) / (2 * N) =
        (1 - (((beta : ℝ) + gamma) / N)) / 2 := by
    field_simp [hn0]
    nlinarith [hsumR]
  have hbg :
      ((beta : ℝ) + gamma) / (2 * N) =
        ((((beta : ℝ) + gamma) / N)) / 2 := by ring
  have ha : (alpha : ℝ) / (2 * N) =
      ((alpha : ℝ) / N) / 2 := by ring
  have hbd :
      ((beta : ℝ) + delta) / (2 * N) =
        (1 - (alpha : ℝ) / N - (gamma : ℝ) / N) / 2 := by
    field_simp [hn0]
    nlinarith [hsumR]
  have hc : (2 * gamma : ℝ) / (2 * N) =
      (gamma : ℝ) / N := by ring
  have hsumE :
      (∑ i : Fin 3, (2 * N : ℝ) *
        ∑ s : Fin 5,
          Real.negMulLog
            ((marginalMultiplicity N alpha beta gamma delta i s : ℝ) /
              (2 * N))) =
      (2 * N : ℝ) *
        (let an := (alpha : ℝ) / N
         let cn := (gamma : ℝ) / N
         let sn := ((beta : ℝ) + gamma) / N
         (3 - cn) * Real.log 2 +
           Real.negMulLog sn + Real.negMulLog (1 - sn) +
           Real.negMulLog an + Real.negMulLog cn +
           Real.negMulLog (1 - an - cn)) := by
    simp only [Fin.sum_univ_succ]
    norm_num [Fin.succ, marginalMultiplicity]
    rw [hhalf, habgd, hbg, ha, hbd, hc]
    rw [henthalf]
    calc
      _ = (2 * N : ℝ) *
          (Real.log 2 +
            2 * Real.negMulLog
              ((((beta : ℝ) + gamma) / N) / 2) +
            2 * Real.negMulLog
              ((1 - (((beta : ℝ) + gamma) / N)) / 2) +
            2 * Real.negMulLog (((alpha : ℝ) / N) / 2) +
            2 * Real.negMulLog
              ((1 - (alpha : ℝ) / N - (gamma : ℝ) / N) / 2) +
            Real.negMulLog ((gamma : ℝ) / N)) := by ring
      _ = _ := by
        rw [hsplit, hsplit, hsplit, hsplit]
        ring
  push_cast at hprod
  rw [hsumE] at hprod
  simpa only [← pow_mul, Nat.reduceMul, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, degree, modeDegree] using hprod

/- Inlined accepted legacy proof: mme_stothers_phi134_four_count_rounding. -/
open Filter

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.Phi134Rounding

private noncomputable def A (a : ℝ) (n : ℕ) : ℕ :=
  ⌊a * (n : ℝ)⌋₊

private noncomputable def C (c : ℝ) (n : ℕ) : ℕ :=
  ⌊c * (n : ℝ)⌋₊

private noncomputable def S (sigma : ℝ) (n : ℕ) : ℕ :=
  ⌊sigma * (n : ℝ)⌋₊

/-- The omitted profile weight `beta = sigma-c`, rounded by subtraction so
it is compatible with the rounded sum `S`. -/
private noncomputable def B (sigma c : ℝ) (n : ℕ) : ℕ :=
  S sigma n - C c n

/-- The omitted profile weight `delta = 1-sigma-a`, used as the exact
remainder so all four integer counts sum to `n`. -/
private noncomputable def D (sigma a : ℝ) (n : ℕ) : ℕ :=
  n - (S sigma n + A a n)

private theorem inline_four_count_rounding_C_le_S
    (sigma c : ℝ) (hcs : c ≤ sigma) (n : ℕ) :
    C c n ≤ S sigma n := by
  unfold C S
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right hcs (Nat.cast_nonneg n)

private theorem inline_four_count_rounding_SA_le
    (sigma a : ℝ) (hsigma : 0 ≤ sigma) (ha : 0 ≤ a)
    (hsa : sigma + a ≤ 1) (n : ℕ) :
    S sigma n + A a n ≤ n := by
  have hS : ((S sigma n : ℕ) : ℝ) ≤ sigma * (n : ℝ) := by
    exact Nat.floor_le (mul_nonneg hsigma (Nat.cast_nonneg n))
  have hA : ((A a n : ℕ) : ℝ) ≤ a * (n : ℝ) := by
    exact Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg n))
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hreal : (((S sigma n + A a n : ℕ) : ℝ)) ≤ (n : ℝ) := by
    push_cast
    calc
      (S sigma n : ℝ) + (A a n : ℝ) ≤
          sigma * (n : ℝ) + a * (n : ℝ) := add_le_add hS hA
      _ = (sigma + a) * (n : ℝ) := by ring
      _ ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hsa hn
      _ = (n : ℝ) := one_mul _
  exact_mod_cast hreal

private theorem inline_four_count_rounding_exact_sum
    (sigma a c : ℝ) (hsigma : 0 ≤ sigma) (ha : 0 ≤ a)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1) (n : ℕ) :
    A a n + B sigma c n + C c n + D sigma a n = n := by
  have hCS := inline_four_count_rounding_C_le_S sigma c hcs n
  have hSA := inline_four_count_rounding_SA_le sigma a hsigma ha hsa n
  unfold B D
  omega

private theorem inline_four_count_rounding_tendsto_A (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ ↦ (A a n : ℝ) / (n : ℝ)) atTop (nhds a) := by
  simpa only [A, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) ha).comp
      tendsto_natCast_atTop_atTop

private theorem inline_four_count_rounding_tendsto_C (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ ↦ (C c n : ℝ) / (n : ℝ)) atTop (nhds c) := by
  simpa only [C, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) hc).comp
      tendsto_natCast_atTop_atTop

private theorem inline_four_count_rounding_tendsto_S (sigma : ℝ) (hsigma : 0 ≤ sigma) :
    Tendsto (fun n : ℕ ↦ (S sigma n : ℝ) / (n : ℝ))
      atTop (nhds sigma) := by
  simpa only [S, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) hsigma).comp
      tendsto_natCast_atTop_atTop

private theorem inline_four_count_rounding_tendsto_B
    (sigma c : ℝ) (hsigma : 0 ≤ sigma) (hc : 0 ≤ c)
    (hcs : c ≤ sigma) :
    Tendsto (fun n : ℕ ↦ (B sigma c n : ℝ) / (n : ℝ))
      atTop (nhds (sigma - c)) := by
  have hraw := (inline_four_count_rounding_tendsto_S sigma hsigma).sub (inline_four_count_rounding_tendsto_C c hc)
  apply hraw.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hCS := inline_four_count_rounding_C_le_S sigma c hcs n
  rw [show B sigma c n = S sigma n - C c n by rfl,
    Nat.cast_sub hCS, sub_div]

private theorem inline_four_count_rounding_tendsto_D
    (sigma a : ℝ) (hsigma : 0 ≤ sigma) (ha : 0 ≤ a)
    (hsa : sigma + a ≤ 1) :
    Tendsto (fun n : ℕ ↦ (D sigma a n : ℝ) / (n : ℝ))
      atTop (nhds (1 - sigma - a)) := by
  have hsum := (inline_four_count_rounding_tendsto_S sigma hsigma).add (inline_four_count_rounding_tendsto_A a ha)
  have hraw : Tendsto
      (fun n : ℕ ↦ (1 : ℝ) -
        ((S sigma n : ℝ) / (n : ℝ) +
          (A a n : ℝ) / (n : ℝ)))
      atTop (nhds (1 - (sigma + a))) :=
    tendsto_const_nhds.sub hsum
  have hD : Tendsto (fun n : ℕ ↦ (D sigma a n : ℝ) / (n : ℝ))
      atTop (nhds (1 - (sigma + a))) := hraw.congr' (by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hSA := inline_four_count_rounding_SA_le sigma a hsigma ha hsa n
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [show D sigma a n = n - (S sigma n + A a n) by rfl,
      Nat.cast_sub hSA, Nat.cast_add, sub_div, div_self hn0]
    ring)
  have hlimit : 1 - (sigma + a) = 1 - sigma - a := by ring
  rw [hlimit] at hD
  exact hD

end MME.StothersFourth.Phi134Rounding

/-- Exact integer profiles approaching every feasible real symmetric
`phi_134` profile.  The construction remains valid when either omitted
weight `sigma-c` or `1-sigma-a` is zero. -/
theorem mme_stothers_phi134_four_count_rounding
    (sigma a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1) :
    ∃ A B C D : ℕ → ℕ,
      (∀ n, A n + B n + C n + D n = n) ∧
      Tendsto (fun n : ℕ ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a) ∧
      Tendsto (fun n : ℕ ↦ (B n : ℝ) / (n : ℝ)) atTop
        (nhds (sigma - c)) ∧
      Tendsto (fun n : ℕ ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c) ∧
      Tendsto (fun n : ℕ ↦ (D n : ℝ) / (n : ℝ)) atTop
        (nhds (1 - sigma - a)) := by
  have hsigma : 0 ≤ sigma := (lt_of_lt_of_le hc hcs).le
  refine ⟨MME.StothersFourth.Phi134Rounding.A a,
    MME.StothersFourth.Phi134Rounding.B sigma c,
    MME.StothersFourth.Phi134Rounding.C c,
    MME.StothersFourth.Phi134Rounding.D sigma a, ?_⟩
  exact ⟨MME.StothersFourth.Phi134Rounding.inline_four_count_rounding_exact_sum
      sigma a c hsigma ha.le hcs hsa,
    MME.StothersFourth.Phi134Rounding.inline_four_count_rounding_tendsto_A a ha.le,
    MME.StothersFourth.Phi134Rounding.inline_four_count_rounding_tendsto_B
      sigma c hsigma hc.le hcs,
    MME.StothersFourth.Phi134Rounding.inline_four_count_rounding_tendsto_C c hc.le,
    MME.StothersFourth.Phi134Rounding.inline_four_count_rounding_tendsto_D
      sigma a hsigma ha.le hsa⟩

/- Inlined accepted legacy proof: mme_stothers_phi134_profile_weight_surplus_over_degree. -/
open MME Real BigOperators Filter
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option warningAsError true

/-- A finite exact Phi134 profile whose component weight beats the sharp
cyclic collision degree and the explicit prime--Behrend loss. -/
theorem mme_stothers_phi134_profile_weight_surplus_over_degree
    (sigma a c L E H V : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H)
    (hV : 0 ≤ V)
    (hVlt :
      V <
        8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))) :
    ∃ N alpha beta gamma delta : ℕ,
      0 < N ∧ alpha + beta + gamma + delta = N ∧
      let D := fun t : Fin 3 ↦
        ∏ s : Fin 5,
          (marginalMultiplicity N alpha beta gamma delta t s).factorial /
            ∏ r : {r : Fin 8 // pattern r t = s},
              (profileMultiplicity alpha beta gamma delta r.1).factorial
      V ^ (2 * N) * (D 0 * (D 1 * D 2) : ℕ) *
          Real.exp (4000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ)) <
        (Nat.card (ExactProfileAddress N alpha beta gamma delta) : ℝ) ^
            (3 : ℕ) *
          (L ^ (2 * beta + 2 * gamma) *
            E ^ (2 * alpha + 2 * beta + 4 * delta) *
            H ^ (2 * gamma)) := by
  classical
  let Z : ℝ :=
    8 *
      ((L / sigma) ^ sigma *
        (E / (1 - sigma)) ^ (1 - sigma)) *
      ((1 / a) ^ a *
        ((H / 2) / c) ^ c *
        (E / (1 - a - c)) ^ (1 - a - c))
  let U : ℝ := (V + Z) / 2
  have hVU : V < U := by dsimp only [U, Z]; linarith
  have hU : 0 < U := lt_of_le_of_lt hV hVU
  have hUZ : U < Z := by dsimp only [U, Z]; linarith
  obtain ⟨A, B, C, D, hsum, hA, hB, hC, hD⟩ :=
    mme_stothers_phi134_four_count_rounding
      sigma a c ha hc hcs hsa
  let modeDegree := fun n : ℕ ↦ fun t : Fin 3 ↦
    ∏ s : Fin 5,
      (marginalMultiplicity n (A n) (B n) (C n) (D n) t s).factorial /
        ∏ r : {r : Fin 8 // pattern r t = s},
          (profileMultiplicity (A n) (B n) (C n) (D n) r.1).factorial
  let degree := fun n : ℕ ↦
    modeDegree n 0 * (modeDegree n 1 * modeDegree n 2)
  let targetCard := fun n : ℕ ↦
    Nat.card (ExactProfileAddress n (A n) (B n) (C n) (D n))
  have hprofileTotal (n : ℕ) :
      ∑ r : Fin 8,
          profileMultiplicity (A n) (B n) (C n) (D n) r = 2 * n := by
    have hnSum := hsum n
    simp [profileMultiplicity, Fin.sum_univ_succ]
    omega
  have htarget (n : ℕ) : 0 < targetCard n := by
    dsimp only [targetCard]
    rw [mme_stothers_phi134_exact_profile_card
      n (A n) (B n) (C n) (D n) (hsum n)]
    have hh := Nat.multinomial_pos Finset.univ
      (profileMultiplicity (A n) (B n) (C n) (D n))
    simpa only [Nat.multinomial, hprofileTotal n] using hh
  have hdegree (n : ℕ) (_hn : 0 < n) : 0 < degree n := by
    have hid := mme_stothers_phi134_capacity_identity
      n (A n) (B n) (C n) (D n) (hsum n)
    change
      (∏ i : Fin 3,
          Nat.multinomial Finset.univ
            (marginalMultiplicity n (A n) (B n) (C n) (D n) i)) *
          degree n = (targetCard n) ^ 3 at hid
    have hrhs : 0 < (targetCard n) ^ 3 := pow_pos (htarget n) 3
    have hproduct : 0 <
        (∏ i : Fin 3,
          Nat.multinomial Finset.univ
            (marginalMultiplicity n (A n) (B n) (C n) (D n) i)) *
          degree n := by
      rw [hid]
      exact hrhs
    exact (CanonicallyOrderedAdd.mul_pos.mp hproduct).2
  have hcapacity (n : ℕ) (hn : 0 < n) :
      Real.exp ((2 * n : ℝ) *
        (let an := (A n : ℝ) / n
         let cn := (C n : ℝ) / n
         let sn := ((B n : ℝ) + C n) / n
         (3 - cn) * Real.log 2 +
           Real.negMulLog sn + Real.negMulLog (1 - sn) +
           Real.negMulLog an + Real.negMulLog cn +
           Real.negMulLog (1 - an - cn))) ≤
        (6 * ((2 * n + 1 : ℕ) : ℝ)) ^ (15 : ℕ) *
          ((targetCard n : ℝ) ^ (3 : ℕ) / (degree n : ℝ)) := by
    simpa only [targetCard, degree, modeDegree] using
      (mme_stothers_phi134_capacity_entropy_lower_bound
        n (A n) (B n) (C n) (D n) hn (hsum n))
  obtain ⟨N, hN, hsumN, hsurplus⟩ :=
    mme_stothers_phi134_analytic_profile_surplus
      sigma a c L E H U A B C D degree targetCard
      ha hc hcs hsa hL hE hH hU hUZ hsum hA hB hC hD
      hdegree hcapacity
  refine ⟨N, A N, B N, C N, D N, hN, hsumN, ?_⟩
  dsimp only
  change
    V ^ (2 * N) * (degree N : ℝ) *
        Real.exp (4000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ)) <
      (targetCard N : ℝ) ^ (3 : ℕ) *
        (L ^ (2 * B N + 2 * C N) *
          E ^ (2 * A N + 2 * B N + 4 * D N) *
          H ^ (2 * C N))
  have hmono := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hV hVU.le (2 * N))
      (by positivity : (0 : ℝ) ≤ (degree N : ℝ)))
    (Real.exp_pos
      (4000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ))).le
  exact hmono.trans_lt hsurplus

/- Inlined accepted legacy proof: mme_stothers_phi134_weighted_isolated_profile_family. -/
open MME Real BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option warningAsError true

/-- The analytic Phi134 surplus, the prime--Behrend labels, and sharp Type-2
isolation combine into a single weighted exact-profile family. -/
theorem mme_stothers_phi134_weighted_isolated_profile_family
    (sigma a c L E H V : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H)
    (hV : 0 ≤ V)
    (hVlt :
      V <
        8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))) :
    ∃ N alpha beta gamma delta : ℕ,
      0 < N ∧ alpha + beta + gamma + delta = N ∧
      ∃ kept : Finset (CyclicExactEdge N alpha beta gamma delta),
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
        (∀ x y z : kept,
          CyclicCoordinatewiseSupported x.1 y.1 z.1 →
            x = y ∧ y = z) ∧
        V ^ (2 * N) <
          (kept.card : ℝ) *
            (L ^ (2 * beta + 2 * gamma) *
              E ^ (2 * alpha + 2 * beta + 4 * delta) *
              H ^ (2 * gamma)) := by
  classical
  obtain ⟨N, alpha, beta, gamma, delta, hN, hsum, hsurplus⟩ :=
    mme_stothers_phi134_profile_weight_surplus_over_degree
      sigma a c L E H V ha hc hcs hsa hL hE hH hV hVlt
  let d : Fin 3 → ℕ := fun t ↦
    ∏ s : Fin 5,
      (marginalMultiplicity N alpha beta gamma delta t s).factorial /
        ∏ r : {r : Fin 8 // pattern r t = s},
          (profileMultiplicity alpha beta gamma delta r.1).factorial
  let D : ℕ := d 0 * (d 1 * d 2)
  let A : ℕ := ∏ i : Fin 3,
    Nat.multinomial Finset.univ
      (marginalMultiplicity N alpha beta gamma delta i)
  let C : ℝ :=
    (Nat.card (ExactProfileAddress N alpha beta gamma delta) : ℝ) ^ (3 : ℕ)
  let F : ℝ := Real.exp (2000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ))
  let B : ℝ :=
    L ^ (2 * beta + 2 * gamma) *
      E ^ (2 * alpha + 2 * beta + 4 * delta) *
      H ^ (2 * gamma)
  change V ^ (2 * N) * (D : ℝ) *
      Real.exp (4000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ)) < C * B at hsurplus
  have hDbounds :=
    mme_stothers_phi134_cyclic_degree_bounds
      N alpha beta gamma delta hsum
  change 1 ≤ D ∧ D ≤ 5 ^ (12 * N) at hDbounds
  have hD : 0 < (D : ℝ) := by
    exact_mod_cast (show 0 < D by omega)
  have hF : 0 < F := by
    dsimp [F]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  obtain ⟨p, hp, hp7, S, hfree, hlarge, hpbound⟩ :=
    mme_stothers_phi134_behrend_prime_of_cyclic_degree
      N alpha beta gamma delta hsum
  have hlarge' : 6 * (D : ℝ) ≤ (S.card : ℝ) := by
    simpa only [D, d, Nat.cast_mul] using hlarge
  have hpbound' : (p : ℝ) ≤ (D : ℝ) * F := by
    simpa only [D, d, F, Nat.cast_mul] using hpbound
  letI : Fact p.Prime := ⟨hp⟩
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  let loss : ℝ :=
    (D : ℝ) * ((S.card : ℝ) / (2 * (p : ℝ) ^ 2))
  have hcancel :
      ((p ^ 2 : ℕ) : ℝ) * loss =
        (D : ℝ) * (S.card : ℝ) / 2 := by
    dsimp [loss]
    push_cast
    field_simp
  have hmargin :
      ((p ^ 2 : ℕ) : ℝ) * loss +
          3 * (D : ℝ) * (D : ℝ) ≤
        (D : ℝ) * (S.card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlarge' hD.le
    rw [hcancel]
    nlinarith
  obtain ⟨q, kept, hkept, hinj, hdiag, hretained⟩ :=
    (mme_stothers_phi134_finite_isolation_of_hash_margin
      hp7 hsum S hfree loss) (by
        simpa only [D, d, Nat.cast_mul] using hmargin)
  have hcapacity :=
    mme_stothers_phi134_capacity_identity
      N alpha beta gamma delta hsum
  change A * D =
    (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 at hcapacity
  have hcapacityR : (A : ℝ) * (D : ℝ) = C := by
    dsimp [C]
    exact_mod_cast hcapacity
  have hcount :
      C * ((S.card : ℝ) / (2 * (p : ℝ) ^ 2)) ≤
        (kept.card : ℝ) := by
    calc
      C * ((S.card : ℝ) / (2 * (p : ℝ) ^ 2)) =
          (A : ℝ) * loss := by
            rw [← hcapacityR]
            dsimp [loss]
            ring
      _ ≤ (kept.card : ℝ) := hretained
  have hFsq :
      F ^ 2 =
        Real.exp (4000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ)) := by
    dsimp [F]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hbudget : V ^ (2 * N) * (D : ℝ) * F ^ 2 < C * B := by
    rw [hFsq]
    exact hsurplus
  have hpden : 0 < 2 * (p : ℝ) ^ 2 := by positivity
  have hcount' :
      C * (S.card : ℝ) ≤
        (kept.card : ℝ) * (2 * (p : ℝ) ^ 2) := by
    apply (div_le_iff₀ hpden).mp
    simpa only [mul_div_assoc] using hcount
  have hleft :
      6 * (D : ℝ) * C ≤
        (kept.card : ℝ) * (2 * (p : ℝ) ^ 2) := by
    have hlabelsC := mul_le_mul_of_nonneg_left hlarge' (by positivity : 0 ≤ C)
    nlinarith
  have hpSq : (p : ℝ) ^ 2 ≤ ((D : ℝ) * F) ^ 2 :=
    pow_le_pow_left₀ hpR.le hpbound' 2
  have hright :
      (kept.card : ℝ) * (2 * (p : ℝ) ^ 2) ≤
        (kept.card : ℝ) * (2 * ((D : ℝ) * F) ^ 2) := by
    gcongr
  have hboth := hleft.trans hright
  have hratio : C ≤ (kept.card : ℝ) * ((D : ℝ) * F ^ 2) := by
    nlinarith [mul_pos hD hF]
  have hweighted := mul_le_mul_of_nonneg_right hratio hB.le
  have hscale : 0 < (D : ℝ) * F ^ 2 := by positivity
  have hfinal : V ^ (2 * N) < (kept.card : ℝ) * B := by
    apply (mul_lt_mul_iff_left₀ hscale).mp
    nlinarith
  exact ⟨N, alpha, beta, gamma, delta, hN, hsum,
    kept, hinj, hdiag, hfinal⟩

/- Inlined accepted legacy proof: mme_stothers_phi134_fine_block_restrict_outer_block. -/
open MME TensorProduct Module

namespace MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem inline_fine_block_restrict_outer_block_canonical_basis_mem_grade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {iota kappa : Type*} [DecidableEq kappa]
    (b : Basis iota K V) (g : iota → kappa) (i : iota) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private theorem inline_fine_block_restrict_outer_block_square_basis_mem_own_grade
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : Fin (q + 2) × Fin (q + 2)) :
    cwSquareCanonicalBasis K q s p ∈
      (cwSquareCanonicalGrading K q).classOf s
        (cwSquarePairGrade q p) := by
  exact Submodule.subset_span ⟨p, rfl, rfl⟩

private theorem inline_fine_block_restrict_outer_block_fourth_basis_apply
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    cwFourthCanonicalBasis K q s p =
      cwSquareCanonicalBasis K q s p.1 ⊗ₜ[K]
        cwSquareCanonicalBasis K q s p.2 := by
  unfold cwFourthCanonicalBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

private theorem inline_fine_block_restrict_outer_block_fourth_basis_mem_own_fine_grade
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
      inline_fine_block_restrict_outer_block_square_basis_mem_own_grade K q s p.1⟩ ⊗ₜ[K]
    ⟨cwSquareCanonicalBasis K q s p.2,
      inline_fine_block_restrict_outer_block_square_basis_mem_own_grade K q s p.2⟩
  have hz := TensorObj.TypeGrading.classKronEmbed_mem
    G G s (cwSquarePairGrade q p.1) (cwSquarePairGrade q p.2) z
  have heq :
      cwFourthCanonicalBasis K q s p =
        TensorObj.TypeGrading.classKronEmbed
          G G s (cwSquarePairGrade q p.1) (cwSquarePairGrade q p.2) z := by
    rw [inline_fine_block_restrict_outer_block_fourth_basis_apply]
    rfl
  rw [heq]
  change
    TensorObj.TypeGrading.classKronEmbed
        G G s (cwSquarePairGrade q p.1) (cwSquarePairGrade q p.2) z ∈
      (TensorObj.TypeGrading.kronGrading G G).classOf s
        (finProdFinEquiv
          (cwSquarePairGrade q p.1, cwSquarePairGrade q p.2))
  exact hz

private theorem inline_fine_block_restrict_outer_block_fine_pair_mem_coarse
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

/-- Inside the fixed coarse type `(1,3,4)`, remembering the first square
grade is equivalent to remembering the complete ordered pair of fine grades. -/
private theorem inline_fine_block_restrict_outer_block_outerGrade_eq_iff_fine_pair
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

private theorem inline_fine_block_restrict_outer_block_outer_blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin 5)
    (p : ModeIndex q s) :
    (outerGrading K q).blockProj s a (canonicalBasis K q s p) =
      if h : outerGrade q s p = a then
        ⟨canonicalBasis K q s p, by
          change canonicalBasis K q s p ∈
            cwBasisGrade (canonicalBasis K q s) (outerGrade q s) a
          simpa only [h] using inline_fine_block_restrict_outer_block_canonical_basis_mem_grade
            (canonicalBasis K q s) (outerGrade q s) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (outerGrading K q) s (outerGrade q s p) _
      (inline_fine_block_restrict_outer_block_canonical_basis_mem_grade
        (canonicalBasis K q s) (outerGrade q s) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (outerGrading K q) s a (outerGrade q s p) (Ne.symm h) _
      (inline_fine_block_restrict_outer_block_canonical_basis_mem_grade
        (canonicalBasis K q s) (outerGrade q s) p)

private theorem inline_fine_block_restrict_outer_block_outer_class_le_fine_comap
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
  have hm := inline_fine_block_restrict_outer_block_fourth_basis_mem_own_fine_grade K q s p.1
  obtain ⟨hx, hy⟩ := (inline_fine_block_restrict_outer_block_outerGrade_eq_iff_fine_pair q sx sy hsum s p).mp hp
  simpa only [hx, hy] using hm

/-- Canonical inclusion of one outer mode block into its literal fine block. -/
private noncomputable def outerClassToFine
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
    (fun x => inline_fine_block_restrict_outer_block_outer_class_le_fine_comap K q sx sy hsum s x.property)

@[simp] private theorem inline_fine_block_restrict_outer_block_outerClassToFine_coe
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) (x : (outerGrading K q).classOf s (sx s)) :
    (outerClassToFine K q sx sy hsum s x).val = x.1.1 := by
  rfl

private theorem inline_fine_block_restrict_outer_block_coarse_blockProj_fourth_basis
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
      simpa only [h] using inline_fine_block_restrict_outer_block_canonical_basis_mem_grade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K q) s (modeTotalGrade s)
      (cwFourthPairGrade q p) (Ne.symm h) _
      (inline_fine_block_restrict_outer_block_canonical_basis_mem_grade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)

private theorem inline_fine_block_restrict_outer_block_fine_blockProj_fourth_basis
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
            inline_fine_block_restrict_outer_block_fourth_basis_mem_own_fine_grade K q s p⟩
      else 0 := by
  let G := TensorObj.TypeGrading.kronGrading
    (cwSquareCanonicalGrading K q) (cwSquareCanonicalGrading K q)
  let own := finProdFinEquiv
    (cwSquarePairGrade q p.1, cwSquarePairGrade q p.2)
  have hp : cwFourthCanonicalBasis K q s p ∈ G.classOf s own :=
    inline_fine_block_restrict_outer_block_fourth_basis_mem_own_fine_grade K q s p
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

private theorem inline_fine_block_restrict_outer_block_outerFine_projection_comp
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) :
    (outerClassToFine K q sx sy hsum s).comp
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
  · have hcproj := inline_fine_block_restrict_outer_block_coarse_blockProj_fourth_basis K q s p
    rw [dif_pos hc] at hcproj
    let pc : ModeIndex q s := ⟨p, hc⟩
    have hcstep := congrArg (fun x =>
      outerClassToFine K q sx sy hsum s
        ((outerGrading K q).blockProj s (sx s) x)) hcproj
    by_cases ho : outerGrade q s pc = sx s
    · have hoproj := inline_fine_block_restrict_outer_block_outer_blockProj_basis K q s (sx s) pc
      rw [dif_pos ho] at hoproj
      have hfine := (inline_fine_block_restrict_outer_block_outerGrade_eq_iff_fine_pair q sx sy hsum s pc).mp ho
      change cwSquarePairGrade q p.1 = sx s ∧
        cwSquarePairGrade q p.2 = sy s at hfine
      have hfproj := inline_fine_block_restrict_outer_block_fine_blockProj_fourth_basis K q s sx sy p
      rw [dif_pos hfine] at hfproj
      calc
        _ = outerClassToFine K q sx sy hsum s
              ((outerGrading K q).blockProj s (sx s)
                (canonicalBasis K q s pc)) := hcstep
        _ = outerClassToFine K q sx sy hsum s
              ⟨canonicalBasis K q s pc, by
                change canonicalBasis K q s pc ∈
                  cwBasisGrade (canonicalBasis K q s)
                    (outerGrade q s) (sx s)
                simpa only [ho] using inline_fine_block_restrict_outer_block_canonical_basis_mem_grade
                  (canonicalBasis K q s) (outerGrade q s) pc⟩ :=
            congrArg (outerClassToFine K q sx sy hsum s) hoproj
        _ = ⟨cwFourthCanonicalBasis K q s p, by
              change cwFourthCanonicalBasis K q s p ∈
                (TensorObj.TypeGrading.kronGrading
                  (cwSquareCanonicalGrading K q)
                  (cwSquareCanonicalGrading K q)).classOf s
                    (finProdFinEquiv (sx s, sy s))
              simpa only [hfine.1, hfine.2] using
                inline_fine_block_restrict_outer_block_fourth_basis_mem_own_fine_grade K q s p⟩ := by
            apply Subtype.ext
            exact canonicalBasis_coe K q s pc
        _ = _ := hfproj.symm
    · have hoproj := inline_fine_block_restrict_outer_block_outer_blockProj_basis K q s (sx s) pc
      rw [dif_neg ho] at hoproj
      have hfine : ¬(cwSquarePairGrade q p.1 = sx s ∧
          cwSquarePairGrade q p.2 = sy s) := by
        intro hp
        exact ho ((inline_fine_block_restrict_outer_block_outerGrade_eq_iff_fine_pair q sx sy hsum s pc).mpr hp)
      have hfproj := inline_fine_block_restrict_outer_block_fine_blockProj_fourth_basis K q s sx sy p
      rw [dif_neg hfine] at hfproj
      calc
        _ = outerClassToFine K q sx sy hsum s
              ((outerGrading K q).blockProj s (sx s)
                (canonicalBasis K q s pc)) := hcstep
        _ = outerClassToFine K q sx sy hsum s 0 :=
          congrArg (outerClassToFine K q sx sy hsum s) hoproj
        _ = 0 := map_zero _
        _ = _ := hfproj.symm
  · have hcproj := inline_fine_block_restrict_outer_block_coarse_blockProj_fourth_basis K q s p
    rw [dif_neg hc] at hcproj
    have hfine : ¬(cwSquarePairGrade q p.1 = sx s ∧
        cwSquarePairGrade q p.2 = sy s) := by
      intro hp
      exact hc (inline_fine_block_restrict_outer_block_fine_pair_mem_coarse q sx sy hsum s p hp)
    have hfproj := inline_fine_block_restrict_outer_block_fine_blockProj_fourth_basis K q s sx sy p
    rw [dif_neg hfine] at hfproj
    calc
      _ = outerClassToFine K q sx sy hsum s
            ((outerGrading K q).blockProj s (sx s) 0) :=
          congrArg (fun x =>
            outerClassToFine K q sx sy hsum s
              ((outerGrading K q).blockProj s (sx s) x)) hcproj
      _ = 0 := by simp only [map_zero]
      _ = _ := hfproj.symm

private theorem inline_fine_block_restrict_outer_block_piTensorMap_three
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

/-- A literal fine block of `phi_134` is a restriction of the matching block
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
  refine ⟨fun s => outerClassToFine K q sx sy hsum s, ?_⟩
  change PiTensorProduct.map
      (fun s => outerClassToFine K q sx sy hsum s)
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
          ((outerClassToFine K q sx sy hsum s).comp
            ((outerGrading K q).blockProj s (sx s))).comp
              ((cwFourthCanonicalGrading K q).blockProj s
                (modeTotalGrade s))) (cwFourthObj K q).t :=
      inline_fine_block_restrict_outer_block_piTensorMap_three
        (fun s => outerClassToFine K q sx sy hsum s)
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
        (inline_fine_block_restrict_outer_block_outerFine_projection_comp K q sx sy hsum s) x

end MME.StothersFourth.Phi134

open MME.StothersFourth.Phi134

set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

theorem mme_stothers_phi134_fine_block_restrict_outer_block
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

/- Inlined accepted legacy proof: mme_stothers_phi134_fine_source_restrict_outer_block. -/
open MME

set_option autoImplicit false
set_option warningAsError true

theorem mme_stothers_phi134_fine_source_restrict_outer_block
    {K : Type u} [Field K] (q : ℕ) (r : Fin 8) :
    TensorObj.Restrict
      (MME.StothersFourth.Phi134.fineSourceObj K q r)
      ((MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor
        (MME.StothersFourth.Phi134.pattern r)) := by
  fin_cases r
  · have hp : MME.StothersFourth.Phi134.pattern (0 : Fin 8) =
        cwSquareBlockType 0 0 4 := by
      funext s
      fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict
      (MME.StothersFourth.Phi134.fineSourceObj K q (0 : Fin 8))
      ((MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor f)) hp).mpr
    exact mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
      (cwSquareBlockType 0 0 4) (cwSquareBlockType 1 3 0)
      (by intro s; fin_cases s <;> rfl)
  · have hp : MME.StothersFourth.Phi134.pattern (1 : Fin 8) =
        cwSquareBlockType 0 1 3 := by
      funext s
      fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict
      (MME.StothersFourth.Phi134.fineSourceObj K q (1 : Fin 8))
      ((MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor f)) hp).mpr
    exact mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
      (cwSquareBlockType 0 1 3) (cwSquareBlockType 1 2 1)
      (by intro s; fin_cases s <;> rfl)
  · have hp : MME.StothersFourth.Phi134.pattern (2 : Fin 8) =
        cwSquareBlockType 0 2 2 := by
      funext s
      fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict
      (MME.StothersFourth.Phi134.fineSourceObj K q (2 : Fin 8))
      ((MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor f)) hp).mpr
    exact mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
      (cwSquareBlockType 0 2 2) (cwSquareBlockType 1 1 2)
      (by intro s; fin_cases s <;> rfl)
  · have hp : MME.StothersFourth.Phi134.pattern (3 : Fin 8) =
        cwSquareBlockType 0 3 1 := by
      funext s
      fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict
      (MME.StothersFourth.Phi134.fineSourceObj K q (3 : Fin 8))
      ((MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor f)) hp).mpr
    exact mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
      (cwSquareBlockType 0 3 1) (cwSquareBlockType 1 0 3)
      (by intro s; fin_cases s <;> rfl)
  · have hp : MME.StothersFourth.Phi134.pattern (4 : Fin 8) =
        cwSquareBlockType 1 0 3 := by
      funext s
      fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict
      (MME.StothersFourth.Phi134.fineSourceObj K q (4 : Fin 8))
      ((MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor f)) hp).mpr
    exact mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
      (cwSquareBlockType 1 0 3) (cwSquareBlockType 0 3 1)
      (by intro s; fin_cases s <;> rfl)
  · have hp : MME.StothersFourth.Phi134.pattern (5 : Fin 8) =
        cwSquareBlockType 1 1 2 := by
      funext s
      fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict
      (MME.StothersFourth.Phi134.fineSourceObj K q (5 : Fin 8))
      ((MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor f)) hp).mpr
    exact mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
      (cwSquareBlockType 1 1 2) (cwSquareBlockType 0 2 2)
      (by intro s; fin_cases s <;> rfl)
  · have hp : MME.StothersFourth.Phi134.pattern (6 : Fin 8) =
        cwSquareBlockType 1 2 1 := by
      funext s
      fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict
      (MME.StothersFourth.Phi134.fineSourceObj K q (6 : Fin 8))
      ((MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor f)) hp).mpr
    exact mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
      (cwSquareBlockType 1 2 1) (cwSquareBlockType 0 1 3)
      (by intro s; fin_cases s <;> rfl)
  · have hp : MME.StothersFourth.Phi134.pattern (7 : Fin 8) =
        cwSquareBlockType 1 3 0 := by
      funext s
      fin_cases s <;> rfl
    apply (congrArg (fun f ↦ TensorObj.Restrict
      (MME.StothersFourth.Phi134.fineSourceObj K q (7 : Fin 8))
      ((MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor f)) hp).mpr
    exact mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
      (cwSquareBlockType 1 3 0) (cwSquareBlockType 0 0 4)
      (by intro s; fin_cases s <;> rfl)

/- Inlined accepted legacy proof: mme_stothers_phi134_exact_fine_word_restrict_outer_address_block. -/
open MME

set_option autoImplicit false
set_option warningAsError true

private theorem inline_exact_fine_word_restrict_outer_address_block_kron_restrict
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

private theorem inline_exact_fine_word_restrict_outer_address_block_kronFin_restrict
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
      exact inline_exact_fine_word_restrict_outer_address_block_kron_restrict hd (h 0)
        (ih (fun r ↦ X r.succ) (fun r ↦ Y r.succ)
          (fun r ↦ h r.succ))

theorem mme_stothers_phi134_exact_fine_word_restrict_outer_address_block
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi134.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi134.fineSourceObj K q
          (MME.StothersFourth.Phi134.exactLabelAt address j)))
      (gradedAddressBlock
        (MME.StothersFourth.Phi134.outerGrading K q) address.1.1) := by
  have h := inline_exact_fine_word_restrict_outer_address_block_kronFin_restrict (K := K) (d := 3) (by omega)
    (2 * N)
    (fun j ↦ MME.StothersFourth.Phi134.fineSourceObj K q
      (MME.StothersFourth.Phi134.exactLabelAt address j))
    (fun j ↦
      (MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor
        (MME.StothersFourth.Phi134.pattern
          (MME.StothersFourth.Phi134.exactLabelAt address j)))
    (fun j ↦ mme_stothers_phi134_fine_source_restrict_outer_block
      (K := K) q (MME.StothersFourth.Phi134.exactLabelAt address j))
  change TensorObj.Restrict _
    (TensorObj.kronFin (2 * N) (fun j ↦
      (MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor
        (fun i ↦ address.1.1 i j)))
  have hfamily :
      (fun j : Fin (2 * N) ↦
        (MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor
          (fun i ↦ address.1.1 i j)) =
      (fun j : Fin (2 * N) ↦
        (MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor
          (MME.StothersFourth.Phi134.pattern
            (MME.StothersFourth.Phi134.exactLabelAt address j))) := by
    funext j
    congr 1
    exact MME.StothersFourth.Phi134.addressType_exactLabelAt address j
  rw [hfamily]
  exact h

/- Inlined accepted legacy proof: mme_stothers_phi134_exact_profile_fine_factorization. -/
open MME

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option warningAsError true

private theorem inline_exact_profile_fine_factorization_pattern_injective :
    Function.Injective MME.StothersFourth.Phi134.pattern := by
  intro r s h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  fin_cases r <;> fin_cases s <;>
    simp [MME.StothersFourth.Phi134.pattern, cwSquareBlockType]
      at h0 h1 h2 ⊢

private theorem inline_exact_profile_fine_factorization_kron_restrict
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

private theorem inline_exact_profile_fine_factorization_kronFin_restrict
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
      exact inline_exact_profile_fine_factorization_kron_restrict hd (h 0)
        (ih (fun r ↦ X r.succ) (fun r ↦ Y r.succ)
          (fun r ↦ h r.succ))

theorem mme_stothers_phi134_exact_profile_fine_factorization
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi134.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin 8 (fun r ↦
        (MME.StothersFourth.Phi134.componentObj K q r).kronPow
          (MME.StothersFourth.Phi134.profileMultiplicity
            alpha beta gamma delta r)))
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi134.fineSourceObj K q
          (MME.StothersFourth.Phi134.exactLabelAt address j))) := by
  classical
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    mme_stothers_phi134_fine_component_restrictions (K := K) q
  have hcomponent : ∀ r : Fin 8,
      TensorObj.Restrict
        (MME.StothersFourth.Phi134.componentObj K q r)
        (MME.StothersFourth.Phi134.fineSourceObj K q r) := by
    intro r
    fin_cases r
    · simpa [MME.StothersFourth.Phi134.componentObj,
        MME.StothersFourth.Phi134.fineSourceObj] using h0
    · simpa [MME.StothersFourth.Phi134.componentObj,
        MME.StothersFourth.Phi134.fineSourceObj] using h1
    · simpa [MME.StothersFourth.Phi134.componentObj,
        MME.StothersFourth.Phi134.fineSourceObj] using h2
    · simpa [MME.StothersFourth.Phi134.componentObj,
        MME.StothersFourth.Phi134.fineSourceObj] using h3
    · simpa [MME.StothersFourth.Phi134.componentObj,
        MME.StothersFourth.Phi134.fineSourceObj] using h4
    · simpa [MME.StothersFourth.Phi134.componentObj,
        MME.StothersFourth.Phi134.fineSourceObj] using h5
    · simpa [MME.StothersFourth.Phi134.componentObj,
        MME.StothersFourth.Phi134.fineSourceObj] using h6
    · simpa [MME.StothersFourth.Phi134.componentObj,
        MME.StothersFourth.Phi134.fineSourceObj] using h7
  have hword : TensorObj.Restrict
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi134.componentObj K q
          (MME.StothersFourth.Phi134.exactLabelAt address j)))
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi134.fineSourceObj K q
          (MME.StothersFourth.Phi134.exactLabelAt address j))) := by
    exact inline_exact_profile_fine_factorization_kronFin_restrict (d := 3) (by omega) (2 * N) _ _
      (fun j ↦ hcomponent
        (MME.StothersFourth.Phi134.exactLabelAt address j))
  have hcard : ∀ r : Fin 8,
      Fintype.card
          {j : Fin (2 * N) //
            MME.StothersFourth.Phi134.exactLabelAt address j = r} =
        MME.StothersFourth.Phi134.profileMultiplicity
          alpha beta gamma delta r := by
    intro r
    rw [Fintype.card_subtype]
    rw [← address.2 r]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      rw [MME.StothersFourth.Phi134.addressType_exactLabelAt, hj]
    · intro hj
      apply inline_exact_profile_fine_factorization_pattern_injective
      rw [← MME.StothersFourth.Phi134.addressType_exactLabelAt address j,
        hj]
  have hgroup := mme_kronFin_group_by_exact_fibers_iso
    (MME.StothersFourth.Phi134.componentObj K q)
    (MME.StothersFourth.Phi134.exactLabelAt address)
    (MME.StothersFourth.Phi134.profileMultiplicity
      alpha beta gamma delta) hcard
  exact TensorObj.Restrict.trans hgroup.2 hword

/- Inlined accepted legacy proof: mme_stothers_phi134_exact_component_product_restrict_outer_address_block. -/
open MME

set_option autoImplicit false
set_option warningAsError true

theorem mme_stothers_phi134_exact_component_product_restrict_outer_address_block
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi134.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin 8 (fun r ↦
        (MME.StothersFourth.Phi134.componentObj K q r).kronPow
          (MME.StothersFourth.Phi134.profileMultiplicity
            alpha beta gamma delta r)))
      (gradedAddressBlock
        (MME.StothersFourth.Phi134.outerGrading K q) address.1.1) := by
  exact TensorObj.Restrict.trans
    (mme_stothers_phi134_exact_profile_fine_factorization
      (K := K) q address)
    (mme_stothers_phi134_exact_fine_word_restrict_outer_address_block
      (K := K) q address)

/- Inlined accepted legacy proof: mme_stothers_phi134_exact_cyclic_component_product_restrict_address_block. -/
open MME

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private theorem inline_exact_cyclic_component_product_restrict_address_block_kron_restrict
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  let P := TensorQ.tensorStrassen K d hd
  have hx : TensorQ.le (TensorQ.toQ X) (TensorQ.toQ X') :=
    (TensorQ.le_toQ X X').2 hX
  have hy : TensorQ.le (TensorQ.toQ Y) (TensorQ.toQ Y') :=
    (TensorQ.le_toQ Y Y').2 hY
  have hleft := P.mul_right _ _ hx (TensorQ.toQ Y)
  have hright := P.mul_right _ _ hy (TensorQ.toQ X')
  apply (TensorQ.le_toQ _ _).1
  rw [TensorQ.toQ_kron, TensorQ.toQ_kron]
  exact P.le_trans _ _ _ hleft (by simpa only [mul_comm] using hright)

theorem mme_stothers_phi134_exact_cyclic_component_product_restrict_address_block
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (e : MME.StothersFourth.Phi134.CyclicExactEdge
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (cyclicSymmetrization
        (TensorObj.kronFin 8 (fun r ↦
          (MME.StothersFourth.Phi134.componentObj K q r).kronPow
            (MME.StothersFourth.Phi134.profileMultiplicity
              alpha beta gamma delta r))))
      (gradedAddressBlock
        (mmeCyclicTripleGrading
          (MME.StothersFourth.Phi134.outerGrading K q))
        (MME.StothersFourth.Phi134.cyclicGradingAddress e)) := by
  let P := TensorObj.kronFin 8 (fun r ↦
    (MME.StothersFourth.Phi134.componentObj K q r).kronPow
      (MME.StothersFourth.Phi134.profileMultiplicity
        alpha beta gamma delta r))
  have hA :=
    mme_stothers_phi134_exact_component_product_restrict_outer_address_block
      (K := K) q e.1
  have hB :=
    mme_stothers_phi134_exact_component_product_restrict_outer_address_block
      (K := K) q e.2.1
  have hC :=
    mme_stothers_phi134_exact_component_product_restrict_outer_address_block
      (K := K) q e.2.2
  have hBperm := TensorObj.permObj_restrict cyclicPerm hB
  have hCperm := TensorObj.permObj_restrict
    (cyclicPerm.trans cyclicPerm) hC
  have hsource : TensorObj.Restrict
      (TensorObj.kron P
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm P)
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) P)))
      (TensorObj.kron
        (gradedAddressBlock
          (MME.StothersFourth.Phi134.outerGrading K q) e.1.1.1)
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm
            (gradedAddressBlock
              (MME.StothersFourth.Phi134.outerGrading K q) e.2.1.1.1))
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (gradedAddressBlock
              (MME.StothersFourth.Phi134.outerGrading K q)
                e.2.2.1.1)))) := by
    apply inline_exact_cyclic_component_product_restrict_address_block_kron_restrict (K := K) (by omega) hA
    exact inline_exact_cyclic_component_product_restrict_address_block_kron_restrict (K := K) (by omega) hBperm hCperm
  have hword := mme_cyclic_grading_address_block_iso
    (MME.StothersFourth.Phi134.outerGrading K q)
    e.1.1.1 e.2.1.1.1 e.2.2.1.1
  rw [cyclicSymmetrization_eq_public_perm]
  exact TensorObj.Restrict.trans hsource hword.1

/- Inlined accepted legacy proof: mme_stothers_phi134_outer_grading_support. -/
open MME TensorProduct PiTensorProduct BigOperators Module

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

namespace MME.StothersFourth.Phi134

private theorem inline_outer_grading_support_basis_mem_cwBasisGrade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι κ : Type*} [DecidableEq κ]
    (b : Basis ι K V) (g : ι -> κ) (i : ι) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private def inline_outer_grading_support_cwVec
    (K : Type u) [Field K] (q : Nat) (s : Fin 3) (a : Fin (q + 2)) :
    CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => (Pi.single a 1 : Fin (q + 2) -> K)
  | ⟨1, _⟩ => (Pi.single a 1 : Fin (q + 2) -> K)
  | ⟨2, _⟩ => (Pi.single a 1 : Fin (q + 2) -> K)

private theorem inline_outer_grading_support_literalTermMonomial_eq_tprod
    (K : Type u) [Field K] (q : Nat)
    (t : CWLiteralTerm q) :
    cwLiteralTermMonomial K q t =
      PiTensorProduct.tprod K
        (fun s => inline_outer_grading_support_cwVec K q s (cwLiteralTermTriple q t s)) := by
  unfold cwLiteralTermMonomial CWMonom
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem inline_outer_grading_support_squareCanonicalBasis_apply
    (K : Type u) [Field K] (q : Nat) (s : Fin 3)
    (a b : Fin (q + 2)) :
    cwSquareCanonicalBasis K q s (a, b) =
      inline_outer_grading_support_cwVec K q s a ⊗ₜ[K] inline_outer_grading_support_cwVec K q s b := by
  letI : IsScalarTower K K (Fin (q + 2) -> K) :=
    IsScalarTower.of_algebraMap_smul (by simp)
  fin_cases s <;>
    change (Module.Basis.tensorProduct (R := K) (S := K)
      (Pi.basisFun K (Fin (q + 2)))
      (Pi.basisFun K (Fin (q + 2)))) (a, b) = _ <;>
    rw [Module.Basis.tensorProduct_apply] <;>
    simp [inline_outer_grading_support_cwVec, Pi.basisFun_apply]

private theorem inline_outer_grading_support_fourthCanonicalBasis_apply
    (K : Type u) [Field K] (q : Nat) (s : Fin 3)
    (p :
      (Fin (q + 2) × Fin (q + 2)) ×
        (Fin (q + 2) × Fin (q + 2))) :
    cwFourthCanonicalBasis K q s p =
      cwSquareCanonicalBasis K q s p.1 ⊗ₜ[K]
        cwSquareCanonicalBasis K q s p.2 := by
  unfold cwFourthCanonicalBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

private theorem inline_outer_grading_support_interchange_tprod
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

private theorem inline_outer_grading_support_fourLiteralTerms_eq_basis_tprod
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
  rw [inline_outer_grading_support_literalTermMonomial_eq_tprod, inline_outer_grading_support_literalTermMonomial_eq_tprod,
    inline_outer_grading_support_literalTermMonomial_eq_tprod, inline_outer_grading_support_literalTermMonomial_eq_tprod,
    inline_outer_grading_support_interchange_tprod, inline_outer_grading_support_interchange_tprod, inline_outer_grading_support_interchange_tprod]
  congr 1
  funext s
  rw [inline_outer_grading_support_fourthCanonicalBasis_apply,
    inline_outer_grading_support_squareCanonicalBasis_apply, inline_outer_grading_support_squareCanonicalBasis_apply]
  rfl

private theorem inline_outer_grading_support_coarse_blockProj_fourth_basis
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
      simpa only [h] using inline_outer_grading_support_basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K q) s (modeTotalGrade s)
      (cwFourthPairGrade q p) (Ne.symm h) _
      (inline_outer_grading_support_basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)

private theorem inline_outer_grading_support_outer_blockProj_basis
    (K : Type u) [Field K] (q : Nat) (s : Fin 3) (a : Fin 5)
    (p : ModeIndex q s) :
    (outerGrading K q).blockProj s a (canonicalBasis K q s p) =
      if h : outerGrade q s p = a then
        ⟨canonicalBasis K q s p, by
          change canonicalBasis K q s p ∈
            cwBasisGrade (canonicalBasis K q s) (outerGrade q s) a
          simpa only [h] using inline_outer_grading_support_basis_mem_cwBasisGrade
            (canonicalBasis K q s) (outerGrade q s) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (outerGrading K q) s (outerGrade q s p) _
      (inline_outer_grading_support_basis_mem_cwBasisGrade
        (canonicalBasis K q s) (outerGrade q s) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (outerGrading K q) s a (outerGrade q s p) (Ne.symm h) _
      (inline_outer_grading_support_basis_mem_cwBasisGrade
        (canonicalBasis K q s) (outerGrade q s) p)

private theorem inline_outer_grading_support_coordGrade_zero (q : Nat) :
    cwSquareCoordGrade q (cwZeroIndex q) = 0 := by
  simp [cwSquareCoordGrade, cwZeroIndex]

private theorem inline_outer_grading_support_coordGrade_middle (q : Nat) (i : Fin q) :
    cwSquareCoordGrade q (cwMiddleIndex q i) = 1 := by
  simp [cwSquareCoordGrade, cwMiddleIndex]
  omega

private theorem inline_outer_grading_support_coordGrade_top (q : Nat) :
    cwSquareCoordGrade q (cwTopIndex q) = 2 := by
  simp [cwSquareCoordGrade, cwTopIndex]

private theorem inline_outer_grading_support_literalTerm_grade_sum_two
    (q : Nat) (t : CWLiteralTerm q) :
    (cwSquareCoordGrade q (cwLiteralTermTriple q t 0)).val +
      (cwSquareCoordGrade q (cwLiteralTermTriple q t 1)).val +
      (cwSquareCoordGrade q (cwLiteralTermTriple q t 2)).val = 2 := by
  rcases t with ⟨i, r⟩ | r <;> fin_cases r <;>
    simp [cwLiteralTermTriple, inline_outer_grading_support_coordGrade_zero,
      inline_outer_grading_support_coordGrade_middle, inline_outer_grading_support_coordGrade_top]

private def inline_outer_grading_support_firstSquareType (q : Nat)
    (t₁ t₂ : CWLiteralTerm q) (s : Fin 3) : Fin 5 :=
  cwSquarePairGrade q
    (cwLiteralTermTriple q t₁ s, cwLiteralTermTriple q t₂ s)

private def inline_outer_grading_support_secondSquareType (q : Nat)
    (t₃ t₄ : CWLiteralTerm q) (s : Fin 3) : Fin 5 :=
  cwSquarePairGrade q
    (cwLiteralTermTriple q t₃ s, cwLiteralTermTriple q t₄ s)

private theorem inline_outer_grading_support_firstSquareType_grade_sum_four
    (q : Nat) (t₁ t₂ : CWLiteralTerm q) :
    (inline_outer_grading_support_firstSquareType q t₁ t₂ 0).val +
      (inline_outer_grading_support_firstSquareType q t₁ t₂ 1).val +
      (inline_outer_grading_support_firstSquareType q t₁ t₂ 2).val = 4 := by
  have h₁ := inline_outer_grading_support_literalTerm_grade_sum_two q t₁
  have h₂ := inline_outer_grading_support_literalTerm_grade_sum_two q t₂
  simp only [inline_outer_grading_support_firstSquareType, cwSquarePairGrade]
  omega

private theorem inline_outer_grading_support_secondSquareType_grade_sum_four
    (q : Nat) (t₃ t₄ : CWLiteralTerm q) :
    (inline_outer_grading_support_secondSquareType q t₃ t₄ 0).val +
      (inline_outer_grading_support_secondSquareType q t₃ t₄ 1).val +
      (inline_outer_grading_support_secondSquareType q t₃ t₄ 2).val = 4 := by
  have h₃ := inline_outer_grading_support_literalTerm_grade_sum_two q t₃
  have h₄ := inline_outer_grading_support_literalTerm_grade_sum_two q t₄
  simp only [inline_outer_grading_support_secondSquareType, cwSquarePairGrade]
  omega

private theorem inline_outer_grading_support_fourLiteralTerms_outer_pattern
    (q : Nat) (t₁ t₂ t₃ t₄ : CWLiteralTerm q)
    (hcoarse : ∀ s,
      cwFourthPairGrade q (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s) =
        modeTotalGrade s) :
    ∃ r : Fin 8,
      (fun s => inline_outer_grading_support_firstSquareType q t₁ t₂ s) = pattern r := by
  have hfirst := inline_outer_grading_support_firstSquareType_grade_sum_four q t₁ t₂
  have hsecond := inline_outer_grading_support_secondSquareType_grade_sum_four q t₃ t₄
  have hiVal := congrArg Fin.val (hcoarse 0)
  have hjVal := congrArg Fin.val (hcoarse 1)
  have hkVal := congrArg Fin.val (hcoarse 2)
  have hi : (inline_outer_grading_support_firstSquareType q t₁ t₂ 0).val +
      (inline_outer_grading_support_secondSquareType q t₃ t₄ 0).val = 1 := by
    simpa [inline_outer_grading_support_firstSquareType, inline_outer_grading_support_secondSquareType, cwFourthPairGrade,
      cwFourthIndexOfLiteralTerms, modeTotalGrade, cwFourthBlockType] using hiVal
  have hj : (inline_outer_grading_support_firstSquareType q t₁ t₂ 1).val +
      (inline_outer_grading_support_secondSquareType q t₃ t₄ 1).val = 3 := by
    simpa [inline_outer_grading_support_firstSquareType, inline_outer_grading_support_secondSquareType, cwFourthPairGrade,
      cwFourthIndexOfLiteralTerms, modeTotalGrade, cwFourthBlockType] using hjVal
  have hk : (inline_outer_grading_support_firstSquareType q t₁ t₂ 2).val +
      (inline_outer_grading_support_secondSquareType q t₃ t₄ 2).val = 4 := by
    simpa [inline_outer_grading_support_firstSquareType, inline_outer_grading_support_secondSquareType, cwFourthPairGrade,
      cwFourthIndexOfLiteralTerms, modeTotalGrade, cwFourthBlockType] using hkVal
  rcases mme_stothers_phi134_square_support_pair_classification
      (inline_outer_grading_support_firstSquareType q t₁ t₂ 0)
      (inline_outer_grading_support_firstSquareType q t₁ t₂ 1)
      (inline_outer_grading_support_firstSquareType q t₁ t₂ 2)
      (inline_outer_grading_support_secondSquareType q t₃ t₄ 0)
      (inline_outer_grading_support_secondSquareType q t₃ t₄ 1)
      (inline_outer_grading_support_secondSquareType q t₃ t₄ 2)
      hfirst hsecond hi hj hk with
    h | h | h | h | h | h | h | h
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
  · refine ⟨6, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨7, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]

private theorem inline_outer_grading_support_projected_literal_zero_of_no_pattern
    (K : Type u) [Field K] (q : Nat)
    (sigma : Fin 3 -> Fin 5)
    (hunsupported : ∀ r : Fin 8, sigma ≠ pattern r)
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
      exact congrArg F (inline_outer_grading_support_fourLiteralTerms_eq_basis_tprod K q t₁ t₂ t₃ t₄)
    _ = 0 := by
      dsimp only [F]
      rw [PiTensorProduct.map_tprod]
      erw [PiTensorProduct.map_tprod]
      by_cases hcoarse : ∀ s,
          cwFourthPairGrade q
              (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s) =
            modeTotalGrade s
      · obtain ⟨r, hr⟩ := inline_outer_grading_support_fourLiteralTerms_outer_pattern
          q t₁ t₂ t₃ t₄ hcoarse
        have haddress :
            (fun s => inline_outer_grading_support_firstSquareType q t₁ t₂ s) ≠ sigma := by
          intro heq
          exact hunsupported r (heq.symm.trans hr)
        have hdiff : ∃ s,
            inline_outer_grading_support_firstSquareType q t₁ t₂ s ≠ sigma s := by
          by_contra hnone
          push Not at hnone
          exact haddress (funext hnone)
        obtain ⟨s, hs⟩ := hdiff
        apply (PiTensorProduct.tprod K).map_coord_zero s
        rw [inline_outer_grading_support_coarse_blockProj_fourth_basis, dif_pos (hcoarse s)]
        let pc : ModeIndex q s :=
          ⟨cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s, hcoarse s⟩
        change (outerGrading K q).blockProj s (sigma s)
          (canonicalBasis K q s pc) = 0
        rw [inline_outer_grading_support_outer_blockProj_basis, dif_neg]
        simpa [pc, outerGrade, inline_outer_grading_support_firstSquareType,
          cwFourthIndexOfLiteralTerms] using hs
      · push Not at hcoarse
        obtain ⟨s, hs⟩ := hcoarse
        apply (PiTensorProduct.tprod K).map_coord_zero s
        rw [inline_outer_grading_support_coarse_blockProj_fourth_basis, dif_neg hs]
        simp

private theorem inline_outer_grading_support_linearMap_pair_fintype_sum
    {R I M N P : Type*} [Semiring R] [Fintype I]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    (A : N →ₗ[R] P) (B : M →ₗ[R] N) (f : I → M) :
    A (B (∑ i, f i)) = ∑ i, A (B (f i)) := by
  rw [map_sum B, map_sum A]

private theorem inline_outer_grading_support_outer_block_zero_of_no_pattern
    (K : Type u) [Field K] (q : Nat)
    (sigma : Fin 3 -> Fin 5)
    (hunsupported : ∀ r : Fin 8, sigma ≠ pattern r) :
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
      exact inline_outer_grading_support_linearMap_pair_fintype_sum A B f₄
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
          exact inline_outer_grading_support_linearMap_pair_fintype_sum A B f₃
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
              exact inline_outer_grading_support_linearMap_pair_fintype_sum A B f₂
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
                  exact inline_outer_grading_support_linearMap_pair_fintype_sum A B f₁
                _ = 0 := by
                  apply Fintype.sum_eq_zero
                  intro t₁
                  dsimp only [A, B, f₁]
                  exact inline_outer_grading_support_projected_literal_zero_of_no_pattern
                    K q sigma hunsupported t₁ t₂ t₃ t₄

end MME.StothersFourth.Phi134

theorem mme_stothers_phi134_outer_grading_support
    {K : Type u} [Field K] (q : Nat) (sigma : Fin 3 -> Fin 5)
    (h : (MME.StothersFourth.Phi134.outerGrading K q).blockTensor sigma ≠ 0) :
    ∃ r : Fin 8, sigma = MME.StothersFourth.Phi134.pattern r := by
  by_contra hnone
  push Not at hnone
  exact h (MME.StothersFourth.Phi134.inline_outer_grading_support_outer_block_zero_of_no_pattern
    K q sigma hnone)

/- Inlined accepted legacy proof: mme_stothers_phi134_induced_exact_profile_blocks_restrict. -/
open MME BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 10000

private theorem inline_induced_exact_profile_blocks_restrict_cyclic_nonzero_supported_core
    {K : Type u} [Field K] {N alpha beta gamma delta : ℕ}
    (es : Fin 3 → CyclicExactEdge N alpha beta gamma delta)
    (hblocks : ∀ j : Fin (2 * N),
      (mmeCyclicTripleGrading (outerGrading K 6)).blockTensor
        (fun i ↦ cyclicGradingAddress (es i) i j) ≠ 0) :
    CyclicCoordinatewiseSupported (es 0) (es 1) (es 2) := by
  let rhoX : Fin 3 → Fin (2 * N) → Fin 5 := fun s ↦
    (es s).1.1.1 s
  let rhoY : Fin 3 → Fin (2 * N) → Fin 5 := fun s ↦
    (es (cyclicPerm s)).2.1.1.1 s
  let rhoZ : Fin 3 → Fin (2 * N) → Fin 5 := fun s ↦
    (es ((cyclicPerm.trans cyclicPerm) s)).2.2.1.1 s
  have hfactors : ∀ j : Fin (2 * N),
      (outerGrading K 6).blockTensor (fun s ↦ rhoX s j) ≠ 0 ∧
      (outerGrading K 6).blockTensor (fun s ↦ rhoY s j) ≠ 0 ∧
      (outerGrading K 6).blockTensor (fun s ↦ rhoZ s j) ≠ 0 := by
    intro j
    apply mme_cyclic_triple_grading_nonzero_factors
      (outerGrading K 6)
        (fun s ↦ rhoX s j) (fun s ↦ rhoY s j) (fun s ↦ rhoZ s j)
    have hgrade :
        (fun i ↦ cyclicGradingAddress (es i) i j) =
          mmeCyclicTripleGrade
            (fun s ↦ rhoX s j) (fun s ↦ rhoY s j)
              (fun s ↦ rhoZ s j) := by
      funext i
      fin_cases i <;> rfl
    rw [← hgrade]
    exact hblocks j
  refine ⟨?_, ?_, ?_⟩
  · intro j
    obtain ⟨r, hr⟩ :=
      mme_stothers_phi134_outer_grading_support
        6 (fun s ↦ rhoX s j) (hfactors j).1
    refine ⟨r, ?_⟩
    calc
      addressType (mixedAddress (es 0).1.1 (es 1).1.1 (es 2).1.1) j =
          (fun s ↦ rhoX s j) := by
            funext i
            fin_cases i <;> rfl
      _ = pattern r := hr
  · intro j
    obtain ⟨r, hr⟩ :=
      mme_stothers_phi134_outer_grading_support
        6 (fun s ↦ rhoY s j) (hfactors j).2.1
    refine ⟨r, ?_⟩
    calc
      addressType
          (mixedAddress (es 1).2.1.1 (es 2).2.1.1 (es 0).2.1.1) j =
          (fun s ↦ rhoY s j) := by
            funext i
            fin_cases i <;> rfl
      _ = pattern r := hr
  · intro j
    obtain ⟨r, hr⟩ :=
      mme_stothers_phi134_outer_grading_support
        6 (fun s ↦ rhoZ s j) (hfactors j).2.2
    refine ⟨r, ?_⟩
    calc
      addressType
          (mixedAddress (es 2).2.2.1 (es 0).2.2.1 (es 1).2.2.1) j =
          (fun s ↦ rhoZ s j) := by
            funext i
            fin_cases i <;> rfl
      _ = pattern r := hr

theorem mme_stothers_phi134_induced_exact_profile_blocks_restrict
    {K : Type u} [Field K] {N alpha beta gamma delta : ℕ}
    (kept : Finset (CyclicExactEdge N alpha beta gamma delta))
    (hdiag : ∀ x y z : kept,
      CyclicCoordinatewiseSupported x.1 y.1 z.1 → x = y ∧ y = z) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin kept.card ↦
        cyclicSymmetrization
          (TensorObj.kronFin 8 (fun r ↦
            (componentObj K 6 r).kronPow
              (profileMultiplicity alpha beta gamma delta r)))))
      ((cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)).kronPow
          (2 * N)) := by
  classical
  let A := fun j : Fin kept.card ↦
    cyclicGradingAddress (kept.equivFin.symm j).1
  have hind (js : Fin 3 → Fin kept.card)
      (hnz : ∀ r,
        (mmeCyclicTripleGrading (outerGrading K 6)).blockTensor
          (fun i ↦ A (js i) i r) ≠ 0) :
      ∃ j, js = fun _ ↦ j := by
    let es := fun i ↦ kept.equivFin.symm (js i)
    have hs := inline_induced_exact_profile_blocks_restrict_cyclic_nonzero_supported_core
      (K := K) (fun i ↦ (es i).1) (by
        intro j
        exact hnz j)
    obtain ⟨h01, h12⟩ := hdiag (es 0) (es 1) (es 2) hs
    have hj01 : js 0 = js 1 := kept.equivFin.symm.injective h01
    have hj12 : js 1 = js 2 := kept.equivFin.symm.injective h12
    refine ⟨js 0, ?_⟩
    funext i
    fin_cases i <;> simp_all
  have hh := mme_induced_graded_address_blocks_restrict
    (mmeCyclicTripleGrading (outerGrading K 6)) A hind
  refine TensorObj.Restrict.trans (mme_bigAdd_mono_restrict ?_) hh
  intro j
  exact
    mme_stothers_phi134_exact_cyclic_component_product_restrict_address_block
      6 (kept.equivFin.symm j).1

/- Inlined accepted legacy proof: mme_stothers_phi134_exact_profile_product_cyclic_value_below. -/
open MME BigOperators Filter
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

private theorem inline_exact_profile_product_cyclic_value_below_component_zero_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (0 : Fin 8) = MMObj K 1 12 1 := by
  unfold componentObj
  rw [Matrix.cons_val_zero]

private theorem inline_exact_profile_product_cyclic_value_below_component_one_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (1 : Fin 8) =
      TensorObj.kron (MMObj K 1 1 12)
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)) := by
  unfold componentObj
  rw [show (1 : Fin 8) = (0 : Fin 7).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]

private theorem inline_exact_profile_product_cyclic_value_below_component_two_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (2 : Fin 8) =
      TensorObj.kron (MMObj K 1 1 38) (coupledObj K 6) := by
  unfold componentObj
  rw [show (2 : Fin 8) = (1 : Fin 7).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (1 : Fin 7) = (0 : Fin 6).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

private theorem inline_exact_profile_product_cyclic_value_below_component_three_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (3 : Fin 8) = MMObj K 12 1 12 := by
  unfold componentObj
  rw [show (3 : Fin 8) = (2 : Fin 7).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (2 : Fin 7) = (1 : Fin 6).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (1 : Fin 6) = (0 : Fin 5).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]

private theorem inline_exact_profile_product_cyclic_value_below_component_four_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (4 : Fin 8) = MMObj K 12 1 12 := by
  unfold componentObj
  rw [show (4 : Fin 8) = (3 : Fin 7).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (3 : Fin 7) = (2 : Fin 6).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (2 : Fin 6) = (1 : Fin 5).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (1 : Fin 5) = (0 : Fin 4).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]

private theorem inline_exact_profile_product_cyclic_value_below_component_five_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (5 : Fin 8) =
      TensorObj.kron (coupledObj K 6) (MMObj K 1 1 38) := by
  unfold componentObj
  rw [show (5 : Fin 8) = (4 : Fin 7).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (4 : Fin 7) = (3 : Fin 6).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (3 : Fin 6) = (2 : Fin 5).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (2 : Fin 5) = (1 : Fin 4).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (1 : Fin 4) = (0 : Fin 3).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

private theorem inline_exact_profile_product_cyclic_value_below_component_six_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (6 : Fin 8) =
      TensorObj.kron
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6))
        (MMObj K 1 1 12) := by
  unfold componentObj
  rw [show (6 : Fin 8) = (5 : Fin 7).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (5 : Fin 7) = (4 : Fin 6).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (4 : Fin 6) = (3 : Fin 5).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (3 : Fin 5) = (2 : Fin 4).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (2 : Fin 4) = (1 : Fin 3).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]

private theorem inline_exact_profile_product_cyclic_value_below_component_seven_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (7 : Fin 8) = MMObj K 1 12 1 := by
  unfold componentObj
  rw [show (7 : Fin 8) = (6 : Fin 7).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (6 : Fin 7) = (5 : Fin 6).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (5 : Fin 6) = (4 : Fin 5).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (4 : Fin 5) = (3 : Fin 4).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (3 : Fin 4) = (2 : Fin 3).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (2 : Fin 3) = (1 : Fin 2).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]

private theorem inline_exact_profile_product_cyclic_value_below_value_downward {K : Type u} [Field K]
    (T : TensorObj K 3) (tau B V : ℝ)
    (h : HasTauValueAtLeast T tau B)
    (hV : 0 ≤ V) (hVB : V ≤ B) :
    HasTauValueAtLeast T tau V := by
  refine ⟨hV, ?_⟩
  intro eps heps
  apply (h.2 eps heps).mono
  rintro N ⟨k, a, b, c, hr, hbound⟩
  refine ⟨k, a, b, c, hr, ?_⟩
  by_cases heps1 : eps ≤ 1
  · exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hV hVB _) (by linarith)).trans hbound
  · exact (mul_nonpos_of_nonneg_of_nonpos
      (pow_nonneg hV _) (by linarith)).trans
        (Finset.sum_nonneg (fun _ _ ↦
          Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Strict cyclic tau-value endpoints of the eight `phi_134` fine payloads,
in the source order 004, 013, 022, 031, 103, 112, 121, 130. -/
noncomputable def phi134Endpoint (tau : ℝ) : Fin 8 → ℝ :=
  ![MME.StothersFourth.E 6 tau,
    MME.StothersFourth.E 6 tau * MME.StothersFourth.L 6 tau,
    MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
    MME.StothersFourth.E 6 tau ^ (2 : ℕ),
    MME.StothersFourth.E 6 tau ^ (2 : ℕ),
    MME.StothersFourth.L 6 tau * MME.StothersFourth.H 6 tau,
    MME.StothersFourth.L 6 tau * MME.StothersFourth.E 6 tau,
    MME.StothersFourth.E 6 tau]

private theorem inline_exact_profile_product_cyclic_value_below_endpoint_pos (tau : ℝ) (r : Fin 8) :
    0 < phi134Endpoint tau r := by
  fin_cases r <;>
    simp [phi134Endpoint, MME.StothersFourth.L,
      MME.StothersFourth.E, MME.StothersFourth.H] <;>
    positivity

private theorem inline_exact_profile_product_cyclic_value_below_mmE_value {K : Type u} [Field K]
    (tau V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.E 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 1 1 12)) tau V := by
  have he :
      ((((1 * 1 * 12) * (1 * 1 * 12) * (1 * 1 * 12) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.E 6 tau := by
    norm_num [MME.StothersFourth.E]
    rw [show (1728 : ℝ) = 12 ^ (3 : ℕ) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 12) 3 tau]
    norm_num
  exact inline_exact_profile_product_cyclic_value_below_value_downward _ _ _ _
    (he ▸ mme_MMObj_cyclic_tau_value (K := K) 1 1 12 tau) hV hVB.le

private theorem inline_exact_profile_product_cyclic_value_below_mmEmid_value {K : Type u} [Field K]
    (tau V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.E 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 1 12 1)) tau V := by
  have he :
      ((((1 * 12 * 1) * (1 * 12 * 1) * (1 * 12 * 1) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.E 6 tau := by
    norm_num [MME.StothersFourth.E]
    rw [show (1728 : ℝ) = 12 ^ (3 : ℕ) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 12) 3 tau]
    norm_num
  exact inline_exact_profile_product_cyclic_value_below_value_downward _ _ _ _
    (he ▸ mme_MMObj_cyclic_tau_value (K := K) 1 12 1 tau) hV hVB.le

private theorem inline_exact_profile_product_cyclic_value_below_mmH_value {K : Type u} [Field K]
    (tau V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.H 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 1 1 38)) tau V := by
  have he :
      ((((1 * 1 * 38) * (1 * 1 * 38) * (1 * 1 * 38) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.H 6 tau := by
    norm_num [MME.StothersFourth.H]
    rw [show (54872 : ℝ) = 38 ^ (3 : ℕ) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 38) 3 tau]
    norm_num
  exact inline_exact_profile_product_cyclic_value_below_value_downward _ _ _ _
    (he ▸ mme_MMObj_cyclic_tau_value (K := K) 1 1 38 tau) hV hVB.le

private theorem inline_exact_profile_product_cyclic_value_below_mmE2_value {K : Type u} [Field K]
    (tau V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.E 6 tau ^ (2 : ℕ)) :
    HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 12 1 12)) tau V := by
  have he :
      ((((12 * 1 * 12) * (12 * 1 * 12) * (12 * 1 * 12) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.E 6 tau ^ (2 : ℕ) := by
    norm_num [MME.StothersFourth.E]
    rw [show (2985984 : ℝ) = 12 ^ (6 : ℕ) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 12) 6 tau]
    calc
      (12 : ℝ) ^ ((6 : ℝ) * tau) =
          (12 : ℝ) ^ ((3 * tau) * 2) := by congr 1; ring
      _ = ((12 : ℝ) ^ (3 * tau)) ^ (2 : ℝ) :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 12) _ _
      _ = ((12 : ℝ) ^ (3 * tau)) ^ (2 : ℕ) := Real.rpow_two _
  exact inline_exact_profile_product_cyclic_value_below_value_downward _ _ _ _
    (he ▸ mme_MMObj_cyclic_tau_value (K := K) 12 1 12 tau) hV hVB.le

private theorem inline_exact_profile_product_cyclic_value_below_coupled_value {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.L 6 tau) :
    HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau V :=
  mme_CW_q6_coupled_raw_cyclic_value_below tau htau V hV hVB

private theorem inline_exact_profile_product_cyclic_value_below_rotated_coupled_value {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.L 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6))) tau V :=
  mme_HasTauValueAtLeast_mono_restrict
    (mme_cyclicSymmetrization_isomorphic_cyclic_orbit
      (coupledObj K 6)).2.2
    (inline_exact_profile_product_cyclic_value_below_coupled_value tau htau V hV hVB)

private theorem inline_exact_profile_product_cyclic_value_below_componentEL_left {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.E 6 tau * MME.StothersFourth.L 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kron (MMObj K 1 1 12)
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)))) tau V := by
  apply mme_cyclic_kron_two_strict_below_product
    (MMObj K 1 1 12)
    (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6))
    tau (MME.StothersFourth.E 6 tau) (MME.StothersFourth.L 6 tau)
    (by unfold MME.StothersFourth.E; positivity)
    (by unfold MME.StothersFourth.L; positivity)
    (inline_exact_profile_product_cyclic_value_below_mmE_value tau) (inline_exact_profile_product_cyclic_value_below_rotated_coupled_value tau htau) V hV hVB

private theorem inline_exact_profile_product_cyclic_value_below_componentHL_left {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kron (MMObj K 1 1 38) (coupledObj K 6))) tau V := by
  apply mme_cyclic_kron_two_strict_below_product
    (MMObj K 1 1 38) (coupledObj K 6)
    tau (MME.StothersFourth.H 6 tau) (MME.StothersFourth.L 6 tau)
    (by unfold MME.StothersFourth.H; positivity)
    (by unfold MME.StothersFourth.L; positivity)
    (inline_exact_profile_product_cyclic_value_below_mmH_value tau) (inline_exact_profile_product_cyclic_value_below_coupled_value tau htau) V hV hVB

private theorem inline_exact_profile_product_cyclic_value_below_componentLH_right {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.L 6 tau * MME.StothersFourth.H 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kron (coupledObj K 6) (MMObj K 1 1 38))) tau V := by
  apply mme_cyclic_kron_two_strict_below_product
    (coupledObj K 6) (MMObj K 1 1 38)
    tau (MME.StothersFourth.L 6 tau) (MME.StothersFourth.H 6 tau)
    (by unfold MME.StothersFourth.L; positivity)
    (by unfold MME.StothersFourth.H; positivity)
    (inline_exact_profile_product_cyclic_value_below_coupled_value tau htau) (inline_exact_profile_product_cyclic_value_below_mmH_value tau) V hV hVB

private theorem inline_exact_profile_product_cyclic_value_below_componentLE_right {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.L 6 tau * MME.StothersFourth.E 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kron
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6))
          (MMObj K 1 1 12))) tau V := by
  apply mme_cyclic_kron_two_strict_below_product
    (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6))
    (MMObj K 1 1 12)
    tau (MME.StothersFourth.L 6 tau) (MME.StothersFourth.E 6 tau)
    (by unfold MME.StothersFourth.L; positivity)
    (by unfold MME.StothersFourth.E; positivity)
    (inline_exact_profile_product_cyclic_value_below_rotated_coupled_value tau htau) (inline_exact_profile_product_cyclic_value_below_mmE_value tau) V hV hVB

private theorem inline_exact_profile_product_cyclic_value_below_component_value {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (r : Fin 8) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < phi134Endpoint tau r) :
    HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 r)) tau V := by
  fin_cases r <;> simp only at hVB ⊢
  · change V < phi134Endpoint tau (0 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (0 : Fin 8))) tau V
    rw [inline_exact_profile_product_cyclic_value_below_component_zero_canonical]
    exact inline_exact_profile_product_cyclic_value_below_mmEmid_value (K := K) tau V hV
      (by simpa [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (1 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (1 : Fin 8))) tau V
    rw [inline_exact_profile_product_cyclic_value_below_component_one_canonical]
    exact inline_exact_profile_product_cyclic_value_below_componentEL_left (K := K) tau htau V hV
      (by simpa [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (2 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (2 : Fin 8))) tau V
    rw [inline_exact_profile_product_cyclic_value_below_component_two_canonical]
    exact inline_exact_profile_product_cyclic_value_below_componentHL_left (K := K) tau htau V hV
      (by simpa [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (3 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (3 : Fin 8))) tau V
    rw [inline_exact_profile_product_cyclic_value_below_component_three_canonical]
    exact inline_exact_profile_product_cyclic_value_below_mmE2_value (K := K) tau V hV
      (by simpa [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (4 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (4 : Fin 8))) tau V
    rw [inline_exact_profile_product_cyclic_value_below_component_four_canonical]
    exact inline_exact_profile_product_cyclic_value_below_mmE2_value (K := K) tau V hV
      (by simpa [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (5 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (5 : Fin 8))) tau V
    rw [inline_exact_profile_product_cyclic_value_below_component_five_canonical]
    exact inline_exact_profile_product_cyclic_value_below_componentLH_right (K := K) tau htau V hV
      (by simpa [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (6 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (6 : Fin 8))) tau V
    rw [inline_exact_profile_product_cyclic_value_below_component_six_canonical]
    exact inline_exact_profile_product_cyclic_value_below_componentLE_right (K := K) tau htau V hV
      (by simpa [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (7 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (7 : Fin 8))) tau V
    rw [inline_exact_profile_product_cyclic_value_below_component_seven_canonical]
    exact inline_exact_profile_product_cyclic_value_below_mmEmid_value (K := K) tau V hV
      (by simpa [phi134Endpoint] using hVB)

/-- Every exact symmetric `phi_134` profile block attains the product of its
eight component endpoints. -/
theorem mme_stothers_phi134_exact_profile_product_cyclic_value_below {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (alpha beta gamma delta : ℕ)
    (W : ℝ) (hW : 0 ≤ W)
    (hWB :
      W <
        MME.StothersFourth.L 6 tau ^ (2 * beta + 2 * gamma) *
        MME.StothersFourth.E 6 tau ^
          (2 * alpha + 2 * beta + 4 * delta) *
        MME.StothersFourth.H 6 tau ^ (2 * gamma)) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kronFin 8 (fun r ↦
          (componentObj K 6 r).kronPow
            (profileMultiplicity alpha beta gamma delta r)))) tau W := by
  apply mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
    (componentObj K 6)
    (profileMultiplicity alpha beta gamma delta)
    tau (phi134Endpoint tau) (inline_exact_profile_product_cyclic_value_below_endpoint_pos tau)
    (inline_exact_profile_product_cyclic_value_below_component_value tau htau) W hW
  convert hWB using 1
  simp [Fin.prod_univ_succ, Fin.succ, phi134Endpoint,
    profileMultiplicity, mul_pow, pow_add, pow_mul]
  ring

/- Inlined accepted legacy finite-power certificate. -/
open MME BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 300000

theorem mme_stothers_phi134_finite_power_block_certificate
    {K : Type u} [Field K] (tau sigma a c : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V <
        8 *
          ((MME.StothersFourth.L 6 tau / sigma) ^ sigma *
            (MME.StothersFourth.E 6 tau / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((MME.StothersFourth.H 6 tau / 2) / c) ^ c *
            (MME.StothersFourth.E 6 tau / (1 - a - c)) ^
              (1 - a - c))) :
    ∃ (N alpha beta gamma delta : ℕ),
      0 < N ∧ alpha + beta + gamma + delta = N ∧
      ∃ (kept : Finset
          (CyclicExactEdge N alpha beta gamma delta))
        (block : kept → TensorObj K 3) (B : ℝ),
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j : Fin kept.card ↦
            block (kept.equivFin.symm j)))
          ((cyclicSymmetrization
            (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)).kronPow
              (2 * N)) ∧
        0 ≤ B ∧
        (∀ e : kept, ∀ W : ℝ,
          0 ≤ W → W < B → HasTauValueAtLeast (block e) tau W) ∧
        V ^ (2 * N) < (kept.card : ℝ) * B := by
  classical
  let L := MME.StothersFourth.L 6 tau
  let E := MME.StothersFourth.E 6 tau
  let H := MME.StothersFourth.H 6 tau
  have hL : 0 < L := by
    unfold L MME.StothersFourth.L
    positivity
  have hE : 0 < E := by
    unfold E MME.StothersFourth.E
    positivity
  have hH : 0 < H := by
    unfold H MME.StothersFourth.H
    positivity
  obtain ⟨N, alpha, beta, gamma, delta, hN, hsum,
      kept, hmode, hdiag, hweighted⟩ :=
    mme_stothers_phi134_weighted_isolated_profile_family
      sigma a c L E H V ha hc hcs hsa hL hE hH hV (by
        simpa only [L, E, H] using hVlt)
  let B : ℝ :=
    L ^ (2 * beta + 2 * gamma) *
      E ^ (2 * alpha + 2 * beta + 4 * delta) *
      H ^ (2 * gamma)
  let blockObj : TensorObj K 3 :=
    cyclicSymmetrization
      (TensorObj.kronFin 8 (fun r ↦
        (componentObj K 6 r).kronPow
          (profileMultiplicity alpha beta gamma delta r)))
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨N, alpha, beta, gamma, delta, hN, hsum, kept,
    (fun _ ↦ blockObj), B, hmode, ?_, hB.le, ?_, ?_⟩
  · simpa only [blockObj] using
      (mme_stothers_phi134_induced_exact_profile_blocks_restrict
        (K := K) kept hdiag)
  · intro e W hW hWB
    dsimp only [blockObj]
    exact mme_stothers_phi134_exact_profile_product_cyclic_value_below
      tau htauLower alpha beta gamma delta W hW (by
        simpa only [B, L, E, H] using hWB)
  · simpa only [B] using hweighted
section
open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 7 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)) tau V := by
  intro V hV hVlt
  let E := MME.StothersFourth.E 6 tau
  let H := MME.StothersFourth.H 6 tau
  let L := MME.StothersFourth.L 6 tau
  let sigma := L / (E + L)
  let a := 2 / (2 + 2 * E + H)
  let c := H / (2 + 2 * E + H)
  obtain ⟨h16E, hEH, hHL, hL4H, h224left, h224right⟩ :=
    mme_stothers_q6_EHL_optimizer_regime tau htauLower htauUpper
  have hopt :=
    mme_stothers_remaining_four_optimizer_certificates
      E H L h16E hEH hHL hL4H h224left h224right
  change
    _ ∧
      (0 < a ∧ 0 < c ∧ c ≤ sigma ∧ sigma + a ≤ 1 ∧
        8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c)) =
          4 * (E + L) * (2 + 2 * E + H)) ∧ _ at hopt
  rcases hopt.2.1 with ⟨ha, hc, hcs, hsa, hrate⟩
  have hVltProfile :
      V <
        8 *
          ((MME.StothersFourth.L 6 tau / sigma) ^ sigma *
            (MME.StothersFourth.E 6 tau / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((MME.StothersFourth.H 6 tau / 2) / c) ^ c *
            (MME.StothersFourth.E 6 tau / (1 - a - c)) ^
              (1 - a - c)) := by
    calc
      V < MME.StothersFourth.classValue 6 tau 7 := hVlt
      _ = 4 * (E + L) * (2 + 2 * E + H) := rfl
      _ =
          8 *
            ((L / sigma) ^ sigma *
              (E / (1 - sigma)) ^ (1 - sigma)) *
            ((1 / a) ^ a *
              ((H / 2) / c) ^ c *
              (E / (1 - a - c)) ^ (1 - a - c)) := hrate.symm
      _ =
          8 *
            ((MME.StothersFourth.L 6 tau / sigma) ^ sigma *
              (MME.StothersFourth.E 6 tau / (1 - sigma)) ^ (1 - sigma)) *
            ((1 / a) ^ a *
              ((MME.StothersFourth.H 6 tau / 2) / c) ^ c *
              (MME.StothersFourth.E 6 tau / (1 - a - c)) ^
                (1 - a - c)) := by
          rfl
  obtain ⟨N, alpha, beta, gamma, delta, hN, _hsum,
      kept, block, B, _hmode, hrestrict, hB, hblock, hcountRate⟩ :=
    mme_stothers_phi134_finite_power_block_certificate
      (K := K) tau sigma a c htauLower htauUpper
        ha hc hcs hsa V hV hVltProfile
  let F : Fin kept.card → TensorObj K 3 :=
    fun j ↦ block (kept.equivFin.symm j)
  have hsumValue :
      HasTauValueAtLeast (TensorObj.bigAdd F) tau (V ^ (2 * N)) := by
    apply mme_HasTauValueAtLeast_bigAdd_uniform_strict
      F tau B hB
    · intro j W hW hWB
      exact hblock (kept.equivFin.symm j) W hW hWB
    · exact pow_nonneg hV _
    · simpa only [F] using hcountRate
  have hpower :
      HasTauValueAtLeast
        ((cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)).kronPow
            (2 * N)) tau (V ^ (2 * N)) :=
    mme_HasTauValueAtLeast_mono_restrict
      (by simpa only [F] using hrestrict) hsumValue
  have htwoN : 0 < 2 * N := Nat.mul_pos (by norm_num) hN
  exact mme_HasTauValueAtLeast_kronPow_root
    (cyclicSymmetrization
      (MME.StothersFourth.cwFourthConstituent K 6 1 3 4))
    tau V (2 * N) htwoN hV hpower

end
