-- Prove2me | Theorems.Thm_Deduction_landau_window_ineq_int
-- name    : Deduction.landau_window_ineq_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:13.330878+00:00
-- url     : https://prove2.me/theorems/59fcf911-5696-4132-9950-f1794f72b4cb
-- title:
--   Deduction: landau window ineq int
-- statement:
--   The Deduction construction uses the landau window ineq int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindowIneq.lean#L10-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindowIneq.lean#L10-L25

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauKernelMax
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_landauWindowIneq
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

theorem Deduction.landau_window_ineq_int (k : ℕ) {σ : ℝ} (hσ : 2 < σ) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ)) (Ioi 0) := by sorry
