-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_ParO_curve_at
-- name    : Formalism.L2.Th1.B.ParO.curve_at
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:59.795496+00:00
-- url     : https://prove2.me/theorems/37e5cc4d-f9d1-4788-a66f-8f3fa3eb375d
-- title:
--   Par O: curve at
-- statement:
--   The Par O construction uses the curve at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InVarAddInVarNeZero.lean#L132-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InVarAddInVarNeZero.lean#L132-L144

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

theorem Formalism.L2.Th1.B.ParO.curve_at {ι : Type} {l P ep : PowerSeries K} {c0 : K}
    (hl : PowerSeries.constantCoeff l = 0)
    (h : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2)) (x : ι) :
    MvPowerSeries.X x ^ 2 * (1 + at1 x l ^ 2 * PowerSeries.subst (at1 x l) P) =
      at1 x l ^ 2 * (at1 x ep + MvPowerSeries.C c0 * MvPowerSeries.X x ^ 2) := by sorry
