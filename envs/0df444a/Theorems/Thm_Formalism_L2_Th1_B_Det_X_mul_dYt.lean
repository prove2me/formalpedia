-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Det_X_mul_dYt
-- name    : Formalism.L2.Th1.B.Det.X_mul_dYt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:00:06.433281+00:00
-- url     : https://prove2.me/theorems/b631d090-f4d2-4e49-8c96-e820f266836f
-- title:
--   Det: X mul d Yt
-- statement:
--   The Det construction uses the X mul d Yt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L163-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L163-L170

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Det
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K

theorem Formalism.L2.Th1.B.Det.X_mul_dYt {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) (j : Fin 3) :
    MvPowerSeries.X j * dYt P j =
      6 * Xt P j ^ 2 - MvPowerSeries.C (g2 / 2) * MvPowerSeries.X j ^ 4 + 3 * Yt P j := by sorry
