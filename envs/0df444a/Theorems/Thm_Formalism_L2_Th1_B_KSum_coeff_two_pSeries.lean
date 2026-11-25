-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_KSum_coeff_two_pSeries
-- name    : Formalism.L2.Th1.B.KSum.coeff_two_pSeries
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:01:17.910647+00:00
-- url     : https://prove2.me/theorems/cebd324b-11d4-4a54-85b0-fe4a3ba73e86
-- title:
--   KSum: coeff two p Series
-- statement:
--   The KSum construction uses the coeff two p Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/CoeffTwoPSeries.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/CoeffTwoPSeries.lean#L12-L18

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_GoodModelLattice
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_CoeffTwoPSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.KSum
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)

theorem Formalism.L2.Th1.B.KSum.coeff_two_pSeries (L : PeriodPair) :
    PowerSeries.coeff 2 (pSeries L) = L.g₂ / 20 := by sorry
