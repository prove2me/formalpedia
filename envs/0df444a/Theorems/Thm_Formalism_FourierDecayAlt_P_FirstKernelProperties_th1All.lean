-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FirstKernelProperties_th1All
-- name    : Formalism.FourierDecayAlt.P.FirstKernelProperties.th1All
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:35:29.183413+00:00
-- url     : https://prove2.me/theorems/cc051df2-6900-461b-903e-58052cf3c385
-- title:
--   First Kernel Properties: th1 All
-- statement:
--   The First Kernel Properties construction uses the th1 All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelProperties.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelProperties.lean#L30-L33

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FirstKernelProperties

theorem Formalism.FourierDecayAlt.P.FirstKernelProperties.th1All : Formalism.FourierDecayAlt.A5.Th1Eq ∧ Formalism.FourierDecayAlt.A5.SingleBlockThetaProps := by sorry
