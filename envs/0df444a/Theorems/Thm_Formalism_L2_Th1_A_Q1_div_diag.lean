-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Q1_div_diag
-- name    : Formalism.L2.Th1.A.Q1.div_diag
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:58:04.0871+00:00
-- url     : https://prove2.me/theorems/62d3324f-5a7f-516b-ba53-5f24236df659
-- title:
--   Q1: div diag
-- statement:
--   The Q1 construction uses the div diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/DifferenceLinearCoeff.lean#L74-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/DifferenceLinearCoeff.lean#L74-L111

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DifferenceLinearCoeff
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_div_diag

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

theorem Formalism.L2.Th1.A.Q1.div_diag (H : MvPowerSeries (Fin 2) R)
    (h : H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] = 0) :
    ∃ Q, H = (MvPowerSeries.X 1 - MvPowerSeries.X 0) * Q := by sorry
