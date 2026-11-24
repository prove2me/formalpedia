-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Det_pderiv_right_weierstrass_pair
-- name    : Formalism.L2.Th1.B.Det.pderiv_right_weierstrass_pair
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:00:13.08386+00:00
-- url     : https://prove2.me/theorems/2f7d45a0-04a3-443a-afe5-a58717406829
-- title:
--   Det: pderiv right weierstrass pair
-- statement:
--   The Det construction uses the pderiv right weierstrass pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L180-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L180-L186

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

theorem Formalism.L2.Th1.B.Det.pderiv_right_weierstrass_pair (P : PowerSeries K) {j k : Fin 3} (h : j ≠ k) :
    pd k (wp3 P j k) = MvPowerSeries.X j ^ 2 * dXt P k - 2 * MvPowerSeries.X k * Xt P j := by sorry
