-- Prove2me | Theorems.Thm_Deduction_mertens_upper_psi_bound
-- name    : Deduction.mertens_upper_psi_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:25.446079+00:00
-- url     : https://prove2.me/theorems/04d3e884-2611-4fd3-83da-a7dfc6d770bf
-- title:
--   Deduction: mertens upper psi bound
-- statement:
--   The Deduction construction uses the mertens upper psi bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mertensUpper.lean#L31-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mertensUpper.lean#L31-L70

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mertensUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction

theorem Deduction.mertens_upper_psi_bound (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n + 1 + Real.log N ≤ 3 * N := by sorry
