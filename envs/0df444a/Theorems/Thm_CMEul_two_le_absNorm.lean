-- Prove2me | Theorems.Thm_CMEul_two_le_absNorm
-- name    : CMEul.two_le_absNorm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:03.077627+00:00
-- url     : https://prove2.me/theorems/94a4ab17-b3a5-4dc4-ace4-d644220bd340
-- title:
--   CMEul: two le abs Norm
-- statement:
--   The CMEul construction uses the two le abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/EulerFactorLocal.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/EulerFactorLocal.lean#L12-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorLocal
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
open CMEul
open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

theorem CMEul.two_le_absNorm {F : Type} [Field F] [NumberField F] (v : Ideal (𝓞 F)) (hv : v.IsMaximal) :
    2 ≤ Ideal.absNorm v := by sorry
