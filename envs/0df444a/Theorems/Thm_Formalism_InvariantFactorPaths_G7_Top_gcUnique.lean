-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_gcUnique
-- name    : Formalism.InvariantFactorPaths.G7.Top.gcUnique
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:31.221804+00:00
-- url     : https://prove2.me/theorems/ce2d2aa9-3eb9-45a5-b34e-f1f2adac2553
-- title:
--   Top: gc Unique
-- statement:
--   The Top construction uses the gc Unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/KernelFromKOne.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/KernelFromKOne.lean#L14-L14

import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ExpansionsAtPlaces
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EKernel
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EChain
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7 Formalism.InvariantFactorPaths.G7.Top
open Formalism.InvariantFactorPaths.G7

theorem Formalism.InvariantFactorPaths.G7.Top.gcUnique : GcUnique := by sorry
