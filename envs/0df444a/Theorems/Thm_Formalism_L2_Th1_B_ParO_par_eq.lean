-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_ParO_par_eq
-- name    : Formalism.L2.Th1.B.ParO.par_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:06.781387+00:00
-- url     : https://prove2.me/theorems/db7075fe-2753-44d0-b592-d4de3d056dc2
-- title:
--   Par O: par eq
-- statement:
--   The Par O construction uses the par eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InVarAddInVarNeZero.lean#L200-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InVarAddInVarNeZero.lean#L200-L301

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
variable {K : Type} [NormedField K] [CharZero K]

theorem Formalism.L2.Th1.B.ParO.par_eq (hA : AddSgStar) (hD : PhODef) {g2 g3 s2 c0 : K} {P l i ep : PowerSeries K}
    {F c : MvPowerSeries (Fin 2) K} (hP : IsWp g2 g3 P) (hF : LawLog F l) (hi : IsInv l i)
    (h3 : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2))
    (hc : MvPowerSeries.X 1 ^ 2 * at1 0 ep - MvPowerSeries.X 0 ^ 2 * at1 1 ep = c * F * FI F i) :
    par F i (phO s2 P l) = -fLog (-c) := by sorry
