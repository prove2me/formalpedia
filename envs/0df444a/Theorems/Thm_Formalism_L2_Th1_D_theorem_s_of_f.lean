-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_theorem_s_of_f
-- name    : Formalism.L2.Th1.D.theorem_s_of_f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:22.614138+00:00
-- url     : https://prove2.me/theorems/5d240dc6-c89e-59ad-b144-471d65897e59
-- title:
--   D: theorem s of f
-- statement:
--   The D construction uses the theorem s of f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ThetaIntegerIsSSubstitution.lean#L242-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ThetaIntegerIsSSubstitution.lean#L242-L248

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_ThetaInZIsThetaLog
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_GaussJetBounds_ThmAEntryFull
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGauss
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThetaLogIsSubst
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ThetaIntegerIsSSubstitution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram entLog oneLog thetaZ thetaOne frameJet frameJetOne
  nablaO)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp OmOK lamF thetaLog sSub zLin)

theorem Formalism.L2.Th1.D.theorem_s_of_f : ThmSOfF := by sorry
