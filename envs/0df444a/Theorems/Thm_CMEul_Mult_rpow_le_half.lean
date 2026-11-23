-- Prove2me | Theorems.Thm_CMEul_Mult_rpow_le_half
-- name    : CMEul.Mult.rpow_le_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:51.973718+00:00
-- url     : https://prove2.me/theorems/136c4c84-9332-4051-9ab5-3c7982b8d0d3
-- title:
--   Mult: rpow le half
-- statement:
--   The Mult construction uses the rpow le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/EulerFactorsMultipliable.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/EulerFactorsMultipliable.lean#L76-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorsMultipliable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open CMEul CMEul.Mult
open Formalism.HermitianLatticesTheory

theorem CMEul.Mult.rpow_le_half {x : ℝ} (hx : 2 ≤ x) : x ^ (-(3 / 2 : ℝ)) ≤ 1 / 2 := by sorry
