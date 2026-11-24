-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FirstKernelProperties_first_kernel_periodic_gram_parseval
-- name    : Formalism.FourierDecayAlt.P.FirstKernelProperties.first_kernel_periodic_gram_parseval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:19.033221+00:00
-- url     : https://prove2.me/theorems/991c4be3-2205-45e5-9ce2-b62083a3d6b6
-- title:
--   First Kernel Properties: first kernel periodic gram parseval
-- statement:
--   The First Kernel Properties construction uses the first kernel periodic gram parseval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelProperties.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelProperties.lean#L15-L18

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

theorem Formalism.FourierDecayAlt.P.FirstKernelProperties.first_kernel_periodic_gram_parseval :
    Formalism.FourierDecayAlt.A5.SingleBlockPeriodic ∧ Formalism.FourierDecayAlt.A5.SingleBlockPosSemidef ∧ Formalism.FourierDecayAlt.A5.SingleBlockParseval := by sorry
