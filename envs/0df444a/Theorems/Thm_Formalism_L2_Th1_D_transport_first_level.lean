-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_transport_first_level
-- name    : Formalism.L2.Th1.D.transport_first_level
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:20:49.802076+00:00
-- url     : https://prove2.me/theorems/c8ceb178-d7dc-58ae-b055-fea7ce11670f
-- title:
--   D: transport first level
-- statement:
--   The D construction uses the transport first level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/TransportFirstLevel.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/TransportFirstLevel.lean#L18-L18

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ThetaIntegerIsSSubstitution
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TraceDualExists
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusOnRingA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_TransportFirstLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D

theorem Formalism.L2.Th1.D.transport_first_level : CoboundaryCocycleTransportAlongHom := by sorry
