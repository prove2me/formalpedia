-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_Pair_log_mul
-- name    : Formalism.L2.Th1.D.Pair.log_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:22.975506+00:00
-- url     : https://prove2.me/theorems/d3a71e5e-44eb-42ea-962b-975cd4b5a2c1
-- title:
--   Pair: log mul
-- statement:
--   The Pair construction uses the log mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L201-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L201-L206

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

theorem Formalism.L2.Th1.D.Pair.log_mul {l : ℕ} {c : K} {e : PowerSeries K} (he : IsMul l c e) {τ : Type}
    {a : MvPowerSeries τ K} (ha : constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a e) (lgF K l) =
      C c * PowerSeries.subst a (lgF K l) := by sorry
