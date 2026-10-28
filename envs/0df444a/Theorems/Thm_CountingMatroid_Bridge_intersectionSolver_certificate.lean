-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_intersectionSolver_certificate
-- name    : CountingMatroid.Bridge.intersectionSolver_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:43:53.627991+00:00
-- url     : https://prove2.me/theorems/43e8a16c-8c2d-4be0-a882-b8393934d076
-- title:
--   Counting accuracy and source costs for the explicit intersection solver
-- statement:
--   Specializes the existing estimator accuracy and resource theorems to CountingMatroid.Analysis.IntersectionSearch.intersectionSolver. The existing augmentation proof is valid at every rank, so its direct feasibility contract uses the already proved 100000 coefficient and degree 8 for both source charge bounds. Fixing this named algorithm avoids relying on an unspecified existential solver when constructing a later machine implementation. These are source-model costs, not a concrete bit-machine simulation.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Analysis_FeasibilitySolver_intersectionSolver_correct
import Theorems.Thm_CountingMatroid_Analysis_FeasibilitySolver_commonBaseCount_pos_iff_common_independent
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearchCost_intersectionSolver_bounded
import Theorems.Thm_CountingMatroid_Analysis_ResourceBound_output_resource_bound
import Theorems.Thm_CountingMatroid_Analysis_OutputAccuracy_output_accuracy

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations CountingMatroid.Model.Subroutines
open CountingMatroid.Bridge

/-- Accuracy and source resource bounds for the named augmenting-path solver.
This fixes the implementation to compile, without choosing an unspecified witness. -/
theorem CountingMatroid.Bridge.intersectionSolver_certificate :
    ∃ (C degree : ℕ),
      ∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
        (o₁ o₂ : IndependenceOracle n) (p : InputParams),
        FullGround M₁ M₂ → CommonRank r M₁ M₂ →
        ExactOracle M₁ o₁ → ExactOracle M₂ o₂ →
        let law := Model.Run.outputLaw Analysis.IntersectionSearch.intersectionSolver n r o₁ o₂ p
        let Z : ℚ := commonBaseCount M₁ M₂
        let size := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
          binaryNatLength (Nat.ceil p.δ⁻¹)
        law.toOuterMeasure
            {x | x.1 < (1 - p.ε) * Z ∨ (1 + p.ε) * Z < x.1} ≤
            ENNReal.ofReal (p.δ : ℝ) ∧
        (Z = 0 → ∀ x ∈ law.support, x.1 = 0) ∧
        ∀ x ∈ law.support,
          0 ≤ x.1 ∧
          x.2.oracleCalls ≤ C * (size + 1) ^ degree ∧
          x.2.bitOps ≤ C * (size + 1) ^ degree := by
  sorry
