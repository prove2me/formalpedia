-- Prove2me | Theorems.Thm_Deduction_landau_tails_pow
-- name    : Deduction.landau_tails_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:06.7857+00:00
-- url     : https://prove2.me/theorems/d7793fa3-c4a3-481c-8979-89e32a25d13e
-- title:
--   Deduction: landau tails pow
-- statement:
--   The Deduction construction uses the landau tails pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauTails.lean#L62-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauTails.lean#L62-L78

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

theorem Deduction.landau_tails_pow (k : ℕ) {σ a x c : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (h : x + k * ((σ - a) / a) ≤ c) :
    Real.exp x * (a ^ (k + 1))⁻¹ ≤ Real.exp c / a / σ ^ k := by sorry
