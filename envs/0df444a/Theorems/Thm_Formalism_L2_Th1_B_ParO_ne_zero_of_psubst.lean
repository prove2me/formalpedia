-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_ParO_ne_zero_of_psubst
-- name    : Formalism.L2.Th1.B.ParO.ne_zero_of_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:58.596276+00:00
-- url     : https://prove2.me/theorems/b996b217-cb23-4331-b660-9b3bcbe44980
-- title:
--   Par O: ne zero of psubst
-- statement:
--   The Par O construction uses the ne zero of psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InVarAddInVarNeZero.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InVarAddInVarNeZero.lean#L97-L100

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

theorem Formalism.L2.Th1.B.ParO.ne_zero_of_psubst {ι : Type} {l : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    {U : MvPowerSeries ι K} (h : PowerSeries.subst U l ≠ 0) : U ≠ 0 := by sorry
