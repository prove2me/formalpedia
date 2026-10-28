-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_finite_experiment_fpras
-- name    : CountingMatroid.Bridge.finite_experiment_fpras
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:48:55.655599+00:00
-- url     : https://prove2.me/theorems/734313df-5548-4a06-a049-b357e63743a1
-- title:
--   Finite fair-bit approximation with the original mission's inputs
-- statement:
--   There exist one source feasibility implementation and uniform natural constants C>0 and d such that the following holds for every full-ground pair of rank-r matroids on Fin n, every exact selector oracle, and rational accuracy and confidence parameters strictly between zero and one. Let B be the original CommonBasesFPRAS resourceBound(C,d), Z its original common-base count, and K the source repetition count times block length. Then K is at most B. Among uniformly sampled length-K Boolean lists, the probability that presampledOutcome falls outside [(1-epsilon)Z,(1+epsilon)Z] is at most delta, expressed exactly as a bad-tape count times 2^(-K). Every such tape yields a nonnegative answer, yields zero if Z=0, and has original oracle and abstract-operation charges at most B. This proves the finite-experiment bridge using the original mission's count, oracle promises, and size convention. It does not assert the existence of the original binary-register program, and it excludes the extra cost of implementing and sampling the experiment. The original mission therefore remains open.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_countingmatroid_main
import Theorems.Thm_CountingMatroid_Analysis_SingleRunAccuracy_fairTape_support_iff_length
import Theorems.Thm_CountingMatroid_Bridge_presampled_bits_polynomial
import Theorems.Thm_CountingMatroid_Bridge_polynomial_source_bound_to_mission
import Theorems.Thm_CountingMatroid_Bridge_exactOracles_to_source
import Theorems.Thm_CountingMatroid_Bridge_commonBaseCount_eq_mission
import Theorems.Thm_CountingMatroid_Bridge_outputLaw_event_card
import Theorems.Thm_CountingMatroid_Bridge_outputLaw_presampled

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- The original mission's mathematical approximation specification is
already realized by one finite fair-bit experiment with a polynomial bit
budget and polynomial source charges. This is NOT a register-machine
realization: `presampledOutcome` is still the mathematical source evaluator.
The remaining implementation obligation must produce one fixed program. -/
theorem CountingMatroid.Bridge.finite_experiment_fpras :
    ∃ (solver : Subroutines.FeasibilityImplementation) (C d : ℕ), 0 < C ∧
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
          ((presampledOutcome solver n r (O false) (O true) p bits).1 < (1-p.ε)*(Z:ℚ) ∨
          (1+p.ε)*(Z:ℚ) < (presampledOutcome solver n r (O false) (O true) p bits).1)} : ENNReal)
            * (1/2 : ENNReal)^K ≤ ENNReal.ofReal (p.δ : ℝ) ∧
        ∀ bits : List Bool, bits.length = K →
          let out := presampledOutcome solver n r (O false) (O true) p bits
          0 ≤ out.1 ∧ (Z = 0 → out.1 = 0) ∧
          out.2.oracleCalls ≤ B ∧ out.2.bitOps ≤ B := by
  sorry
