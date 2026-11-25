-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Q1_second
-- name    : Formalism.L2.Th1.A.Q1.second
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:02:01.770112+00:00
-- url     : https://prove2.me/theorems/16cf7198-d1f9-4667-baeb-af47980ce5d0
-- title:
--   Q1: second
-- statement:
--   The Q1 construction uses the second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/DifferenceLinearCoeff.lean#L176-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/DifferenceLinearCoeff.lean#L176-L188

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DifferenceLinearCoeff
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
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem Formalism.L2.Th1.A.Q1.second {n₁ : MvPowerSeries (Fin 2) R} (h : diff2 W = (U₁ - U₂) * n₁) :
    fgl W = (U₂ - (iSer W).subst (U₁ : MvPowerSeries (Fin 2) R))
      * n₁.subst ![(U₂ : MvPowerSeries (Fin 2) R), (iSer W).subst (U₁ : MvPowerSeries (Fin 2) R)] := by sorry
