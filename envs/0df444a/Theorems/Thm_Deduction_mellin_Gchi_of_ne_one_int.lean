-- Prove2me | Theorems.Thm_Deduction_mellin_Gchi_of_ne_one_int
-- name    : Deduction.mellin_Gchi_of_ne_one_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:18.434319+00:00
-- url     : https://prove2.me/theorems/afa88b54-1e95-4974-b426-e0617a223590
-- title:
--   Deduction: mellin Gchi of ne one int
-- statement:
--   The Deduction construction uses the mellin Gchi of ne one int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mellinGchiOfNeOne.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mellinGchiOfNeOne.lean#L19-L25

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_MellinRamp
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiOfNeOne
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

theorem Deduction.mellin_Gchi_of_ne_one_int (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by sorry
