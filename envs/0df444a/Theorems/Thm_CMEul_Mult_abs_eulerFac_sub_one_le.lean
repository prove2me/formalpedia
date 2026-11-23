-- Prove2me | Theorems.Thm_CMEul_Mult_abs_eulerFac_sub_one_le
-- name    : CMEul.Mult.abs_eulerFac_sub_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:33.973154+00:00
-- url     : https://prove2.me/theorems/66cdaca5-f0f8-4007-9f40-ce3d251d5698
-- title:
--   Mult: abs euler Fac sub one le
-- statement:
--   The Mult construction uses the abs euler Fac sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/EulerFactorsMultipliable.lean#L85-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/EulerFactorsMultipliable.lean#L85-L138

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

theorem CMEul.Mult.abs_eulerFac_sub_one_le {K : Type} [Field K] [NumberField K] [StarRing K] (M : ℕ)
    (hM : 3 ≤ M) (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    |eulerFac K M P - 1| ≤ 2 * ((Ideal.absNorm P : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by sorry
