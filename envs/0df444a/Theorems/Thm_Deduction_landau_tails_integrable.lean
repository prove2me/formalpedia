-- Prove2me | Theorems.Thm_Deduction_landau_tails_integrable
-- name    : Deduction.landau_tails_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:34:59.586836+00:00
-- url     : https://prove2.me/theorems/5f416b42-3d7b-4fc5-8972-57e1a94f212b
-- title:
--   Deduction: landau tails integrable
-- statement:
--   The Deduction construction uses the landau tails integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauTails.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauTails.lean#L10-L16

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_kernelIntegral
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_landauTails
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

theorem Deduction.landau_tails_integrable (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-a * u) / (k.factorial : ℝ)) (Ioi 0) := by sorry
