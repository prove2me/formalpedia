-- Prove2me | Theorems.Thm_Deduction_poleData_inv_zero
-- name    : Deduction.poleData_inv_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:38.906586+00:00
-- url     : https://prove2.me/theorems/54cabca8-a332-4ae3-b517-f9ddb347cd93
-- title:
--   Deduction: pole Data inv zero
-- statement:
--   The Deduction construction uses the pole Data inv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean#L241-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean#L241-L246

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LogDerivLocal
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_CharFamilyLFunctionNeZeroOfOneLeRe
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiOfNeOne
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiModOne
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_measurableGchi
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_GchiGrowth
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_GchiConj
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_poleData
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

theorem Deduction.poleData_inv_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ ρ = 0 ↔
      DirichletCharacter.LFunction χ ((starRingEnd ℂ) ρ) = 0 := by sorry
