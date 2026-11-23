-- Prove2me | Theorems.Thm_Deduction_mertens_upper_nat
-- name    : Deduction.mertens_upper_nat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:56.685706+00:00
-- url     : https://prove2.me/theorems/ad851f29-3d21-4043-9956-a24be6c96e41
-- title:
--   Deduction: mertens upper nat
-- statement:
--   The Deduction construction uses the mertens upper nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mertensUpper.lean#L72-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mertensUpper.lean#L72-L101

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

theorem Deduction.mertens_upper_nat (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤ Real.log N + 2 := by sorry
