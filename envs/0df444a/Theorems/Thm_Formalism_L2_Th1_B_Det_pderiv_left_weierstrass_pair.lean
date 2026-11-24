-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Det_pderiv_left_weierstrass_pair
-- name    : Formalism.L2.Th1.B.Det.pderiv_left_weierstrass_pair
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:00:17.732397+00:00
-- url     : https://prove2.me/theorems/56f5fcd7-756b-4bbd-a276-e119157ead6c
-- title:
--   Det: pderiv left weierstrass pair
-- statement:
--   The Det construction uses the pderiv left weierstrass pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L172-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L172-L178

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

theorem Formalism.L2.Th1.B.Det.pderiv_left_weierstrass_pair (P : PowerSeries K) {j k : Fin 3} (h : k ≠ j) :
    pd j (wp3 P j k) = 2 * MvPowerSeries.X j * Xt P k - MvPowerSeries.X k ^ 2 * dXt P j := by sorry
