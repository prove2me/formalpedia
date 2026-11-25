-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Q1_X_one_dvd_of_subst_X_zero_eq_zero
-- name    : Formalism.L2.Th1.A.Q1.X_one_dvd_of_subst_X_zero_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:01:48.828623+00:00
-- url     : https://prove2.me/theorems/2eb3e337-f6f0-4946-b1ff-184fdaba87a2
-- title:
--   Q1: X one dvd of subst X zero eq zero
-- statement:
--   The Q1 construction uses the X one dvd of subst X zero eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/DifferenceLinearCoeff.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/DifferenceLinearCoeff.lean#L67-L72

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DifferenceLinearCoeff
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_X_one_dvd_of_subst_X_zero_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Q1
open CubeR
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} [CommRing R]

theorem Formalism.L2.Th1.A.Q1.X_one_dvd_of_subst_X_zero_eq_zero (H : MvPowerSeries (Fin 2) R)
    (h : H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = 0) :
    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ∣ H := by sorry
