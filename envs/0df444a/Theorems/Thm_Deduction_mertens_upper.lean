-- Prove2me | Theorems.Thm_Deduction_mertens_upper
-- name    : Deduction.mertens_upper
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:20.840715+00:00
-- url     : https://prove2.me/theorems/acaff696-8ddd-408c-b356-bf0568e48141
-- title:
--   Deduction: mertens upper
-- statement:
--   The Deduction construction uses the mertens upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mertensUpper.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mertensUpper.lean#L103-L112

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

theorem Deduction.mertens_upper (y : ℝ) (hy : 1 ≤ y) :
    ∑ n ∈ Finset.range (⌊y⌋₊ + 1), ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤ Real.log y + 2 := by sorry
