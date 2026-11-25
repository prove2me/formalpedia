-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Shape_mem_ball
-- name    : Formalism.L2.Th1.E.Shape.mem_ball
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:48:54.207803+00:00
-- url     : https://prove2.me/theorems/3c9c1057-86b6-5611-bd94-f701a5021dd8
-- title:
--   Shape: mem ball
-- statement:
--   The Shape construction uses the mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ConstantCoeffInvTDen.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ConstantCoeffInvTDen.lean#L23-L24

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SeriesSubgroup
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInvTDen
import Theorems.Thm_Formalism_ELL_VeluIntegrality_mem_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Shape

theorem Formalism.L2.Th1.E.Shape.mem_ball {K : Type} [NormedField K] [IsUltrametricDist K] {a : K} :
    a ∈ ball K ↔ ‖a‖ ≤ 1 := by sorry
