-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_ParO_value_at
-- name    : Formalism.L2.Th1.B.ParO.value_at
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:21.729378+00:00
-- url     : https://prove2.me/theorems/a70222c4-2ad2-4fcc-b309-9fa13100db06
-- title:
--   Par O: value at
-- statement:
--   The Par O construction uses the value at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InVarAddInVarNeZero.lean#L65-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InVarAddInVarNeZero.lean#L65-L74

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParO
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.ParO.value_at {ι : Type} {l g ph : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (hph : PowerSeries.constantCoeff ph = 0)
    (e : PowerSeries.subst l g = PowerSeries.X * fExp (-ph))
    {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0) :
    PowerSeries.subst (PowerSeries.subst U l) g = U * fExp (-PowerSeries.subst U ph) := by sorry
