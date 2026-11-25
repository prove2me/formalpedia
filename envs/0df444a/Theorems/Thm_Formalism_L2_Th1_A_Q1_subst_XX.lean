-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Q1_subst_XX
-- name    : Formalism.L2.Th1.A.Q1.subst_XX
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:59:49.78189+00:00
-- url     : https://prove2.me/theorems/54bdd64a-01a7-5238-8709-cdd4f30f8908
-- title:
--   Q1: subst XX
-- statement:
--   The Q1 construction uses the subst XX property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/DifferenceLinearCoeff.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/DifferenceLinearCoeff.lean#L22-L28

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DifferenceLinearCoeff
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_subst_XX
import Theorems.Thm_Formalism_G_LogP_subst_XX

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

theorem Formalism.L2.Th1.A.Q1.subst_XX (G : MvPowerSeries (Fin 2) R) :
    G.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] = G := by sorry
