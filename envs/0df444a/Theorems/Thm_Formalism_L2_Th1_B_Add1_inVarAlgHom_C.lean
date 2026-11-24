-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Add1_inVarAlgHom_C
-- name    : Formalism.L2.Th1.B.Add1.inVarAlgHom_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.898204+00:00
-- url     : https://prove2.me/theorems/51ec096b-4951-474b-90d7-0bf3ab7d6a07
-- title:
--   Add1: in Var Alg Hom C
-- statement:
--   The Add1 construction uses the in Var Alg Hom C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RestrictSecondZeroInVarOne.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RestrictSecondZeroInVarOne.lean#L21-L24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Add1
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.Add1.inVarAlgHom_C {ι : Type} (x : ι) (c : K) :
    at1H x (PowerSeries.C c) = (MvPowerSeries.C c : MvPowerSeries ι K) := by sorry
