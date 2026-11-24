-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_Pair_addC_log
-- name    : Formalism.L2.Th1.D.Pair.addC_log
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:20.245548+00:00
-- url     : https://prove2.me/theorems/e9f69b7a-150a-495d-abc6-83f0e6bd421d
-- title:
--   Pair: add C log
-- statement:
--   The Pair construction uses the add C log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L85-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L85-L99

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

theorem Formalism.L2.Th1.D.Pair.addC_log (hE : ExpSpec) {l : ℕ} (hl : 2 ≤ l) {τ : Type} {a b : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (be0 : MvPowerSeries (Fin 2) K) :
    subst ![PowerSeries.subst a (lgF K l), PowerSeries.subst b (lgF K l)] (addC l be0) =
      subst ![a, b] be0 := by sorry
