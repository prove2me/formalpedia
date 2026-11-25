-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_linSub_sqSum
-- name    : Formalism.L2.Th1.G.linSub_sqSum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:01.241604+00:00
-- url     : https://prove2.me/theorems/649977ed-c1f5-5d9f-86c4-04b5860220ab
-- title:
--   G: lin Sub sq Sum
-- statement:
--   The G construction uses the lin Sub sq Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Several.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Several.lean#L70-L76

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Several
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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.G.linSub_sqSum {n m : Type} [Fintype n] [Fintype m] (A : n → m → K) (c : n → K) :
    linSub A (sqSum c) =
      ∑ i, MvPowerSeries.C (c i) * (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x) ^ 2 := by sorry
