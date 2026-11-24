-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_Pair_hs3
-- name    : Formalism.L2.Th1.D.Pair.hs3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:23:29.791921+00:00
-- url     : https://prove2.me/theorems/b6bbe41b-2c5e-4024-ad01-0556b4bbb82d
-- title:
--   Pair: hs3
-- statement:
--   The Pair construction uses the hs3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L30-L32

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs3

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.D.Pair.hs3 {τ : Type} {a b c : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (hc : constantCoeff c = 0) : HasSubst ![a, b, c] := by sorry
