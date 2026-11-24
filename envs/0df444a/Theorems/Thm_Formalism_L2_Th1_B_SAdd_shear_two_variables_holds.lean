-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_SAdd_shear_two_variables_holds
-- name    : Formalism.L2.Th1.B.SAdd.shear_two_variables_holds
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:02:00.672826+00:00
-- url     : https://prove2.me/theorems/e9a47bc5-acf7-43ba-9fee-1e4d7a665bca
-- title:
--   SAdd: shear two variables holds
-- statement:
--   The SAdd construction uses the shear two variables holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffQuotientXSq.lean#L117-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffQuotientXSq.lean#L117-L123

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffQuotientXSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.SAdd
open Formalism.InvariantFactorPaths.G7 (at1)

theorem Formalism.L2.Th1.B.SAdd.shear_two_variables_holds : ShearTwo := by sorry
