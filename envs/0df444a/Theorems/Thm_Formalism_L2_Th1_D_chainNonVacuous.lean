-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_chainNonVacuous
-- name    : Formalism.L2.Th1.D.chainNonVacuous
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:47.296809+00:00
-- url     : https://prove2.me/theorems/198c2e6b-3d95-556a-b887-65aa6f0782a7
-- title:
--   D: chain Non Vacuous
-- statement:
--   The D construction uses the chain Non Vacuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/SecondLevelOfNorm.lean#L7-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/SecondLevelOfNorm.lean#L7-L7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NonVac
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SecondLevelOfNormHolds
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_SecondLevelOfNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D

theorem Formalism.L2.Th1.D.chainNonVacuous : ChainNonVacuous := by sorry
