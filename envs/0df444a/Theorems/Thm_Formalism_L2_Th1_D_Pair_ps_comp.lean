-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_Pair_ps_comp
-- name    : Formalism.L2.Th1.D.Pair.ps_comp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:23.238398+00:00
-- url     : https://prove2.me/theorems/2680b017-9722-4a63-af15-a131d11c0e35
-- title:
--   Pair: ps comp
-- statement:
--   The Pair construction uses the ps comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L65-L69

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
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

theorem Formalism.L2.Th1.D.Pair.ps_comp {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0) {e : PowerSeries K}
    (he : PowerSeries.constantCoeff e = 0) (f : PowerSeries K) :
    PowerSeries.subst (PowerSeries.subst a e) f = PowerSeries.subst a (PowerSeries.subst e f) := by sorry
