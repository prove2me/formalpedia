-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_ParO_psubst_fExp
-- name    : Formalism.L2.Th1.B.ParO.psubst_fExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:01.435894+00:00
-- url     : https://prove2.me/theorems/bf2173a7-97c0-4150-81b1-53c24404d069
-- title:
--   Par O: psubst f Exp
-- statement:
--   The Par O construction uses the psubst f Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InVarAddInVarNeZero.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InVarAddInVarNeZero.lean#L54-L59

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

theorem Formalism.L2.Th1.B.ParO.psubst_fExp {ι : Type} {u : MvPowerSeries ι K} (hu : MvPowerSeries.constantCoeff u = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst u (fExp f) = fExp (PowerSeries.subst u f) := by sorry
