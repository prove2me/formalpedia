-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_Pair_log_law
-- name    : Formalism.L2.Th1.D.Pair.log_law
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:21.159161+00:00
-- url     : https://prove2.me/theorems/70ddfafe-019b-4278-b823-aae682cd0d28
-- title:
--   Pair: log law
-- statement:
--   The Pair construction uses the log law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L115-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L115-L128

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

theorem Formalism.L2.Th1.D.Pair.log_law {l : ℕ} {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0)
    (hF : cob F (lgF K l) = 0) {τ : Type} {a b : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    PowerSeries.subst (subst ![a, b] F) (lgF K l) =
      PowerSeries.subst a (lgF K l) + PowerSeries.subst b (lgF K l) := by sorry
