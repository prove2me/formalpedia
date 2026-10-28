-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_finite_experiment_fpras_explicit
-- name    : CountingMatroid.Bridge.finite_experiment_fpras_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:48:24.389737+00:00
-- url     : https://prove2.me/theorems/51cd77c7-babe-4cf1-a29f-c727952bf9a5
-- title:
--   Finite fair-bit counting experiment with an explicit feasibility solver
-- statement:
--   Uses the named capped augmenting-path intersection algorithm for feasibility. There are fixed polynomial constants such that, on every promised input of the original common-bases mission, a polynomial number K of independent fair bits suffices for the existing estimator: the fraction of inaccurate length-K tapes is at most delta; every tape gives a nonnegative estimate, exactly zero if there are no common bases, with polynomial source query and operation charges. Reuses the already proved presampling, parameter comparison, accuracy, and resource lemmas. The remaining obligation is one fixed oracle-aware binary-register program realizing this specific evaluator with polynomial actual bit cost and halting time. This theorem does not assert that machine realization.
--
--   Mathematical proof route: (1) The existing capped annealing analysis bounds one run's failure probability by 1/4, and independent median amplification reduces it to delta. The explicit intersection solver handles the zero-count case. (2) Sample K = repetitions * blockLength fair bits upfront and split them into the prescribed blocks. The proved distribution identity preserves the source evaluator exactly, including its default-false reads. The schedule envelope and input-size comparison bound K by a polynomial in the original mission parameters. (3) Implement this deterministic evaluator using finite bit-vector sets, finite arrays, and canonical binary rationals. Existing rational-size invariants and explicit loop caps supply bounds to reuse; actual arithmetic, normalization, storage, and loop overhead still require machine-realization proofs. (4) Use a balanced physical sampler with input-determined coin positions. Among B clock bits, each K-bit sample has 2^(B-K) extensions, preserving the failure fraction. A polynomial all-tape halting bound and absorbing halt states then transfer the estimate to the original observation time B. Steps (1) and (2) are certified here; the concrete program and cost obligations in (3) and (4) remain open.
--
--   Reuse audit: the proved NLogN.compile_correct theorem (https://prove2.me/theorems/646dfea8-02f6-4eca-beca-52d2d6952814) is a candidate for encoded integers and structured control. Its inspected language has no external oracle instruction, and its Fin-16 symbol stacks need a binary encoding adapter. Its existing theorem is not itself a proof of the original mission's oracle machine requirement.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Bridge_presampled_bits_polynomial
import Theorems.Thm_CountingMatroid_Bridge_polynomial_source_bound_to_mission
import Theorems.Thm_CountingMatroid_Bridge_exactOracles_to_source
import Theorems.Thm_CountingMatroid_Bridge_commonBaseCount_eq_mission
import Theorems.Thm_CountingMatroid_Bridge_outputLaw_event_card
import Theorems.Thm_CountingMatroid_Bridge_outputLaw_presampled
import Theorems.Thm_CountingMatroid_Analysis_SingleRunAccuracy_fairTape_support_iff_length
import Theorems.Thm_CountingMatroid_Bridge_intersectionSolver_certificate

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations CountingMatroid.Model.Subroutines
open CountingMatroid.Bridge

/-- The finite-experiment certificate with an explicit deterministic feasibility
algorithm. It still leaves concrete register-machine realization to a later proof. -/
theorem CountingMatroid.Bridge.finite_experiment_fpras_explicit :
    ∃ (C d : ℕ), 0 < C ∧
      ∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
        (O : OAI.CommonBasesFPRAS.IndependenceOracle n) (p : InputParams),
        M₁.E = Set.univ → M₂.E = Set.univ →
        M₁.eRank = (r : ℕ∞) → M₂.eRank = (r : ℕ∞) →
        OAI.CommonBasesFPRAS.ExactOracles M₁ M₂ O →
        let K := (Program.schedule n p).val.repetitions * blockLength n r p
        let B := OAI.CommonBasesFPRAS.resourceBound C d n r p.ε p.δ
        let Z := OAI.CommonBasesFPRAS.commonBaseCount M₁ M₂
        K ≤ B ∧
        (Set.ncard {bits : List Bool | bits.length = K ∧
          ((presampledOutcome Analysis.IntersectionSearch.intersectionSolver n r (O false) (O true) p bits).1 < (1-p.ε)*(Z:ℚ) ∨
          (1+p.ε)*(Z:ℚ) < (presampledOutcome Analysis.IntersectionSearch.intersectionSolver n r (O false) (O true) p bits).1)} : ENNReal)
            * (1/2 : ENNReal)^K ≤ ENNReal.ofReal (p.δ : ℝ) ∧
        ∀ bits : List Bool, bits.length = K →
          let out := presampledOutcome Analysis.IntersectionSearch.intersectionSolver n r (O false) (O true) p bits
          0 ≤ out.1 ∧ (Z = 0 → out.1 = 0) ∧
          out.2.oracleCalls ≤ B ∧ out.2.bitOps ≤ B := by
  sorry
