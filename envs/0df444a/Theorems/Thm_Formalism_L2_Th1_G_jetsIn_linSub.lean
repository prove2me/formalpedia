-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_jetsIn_linSub
-- name    : Formalism.L2.Th1.G.jetsIn_linSub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:37:19.289687+00:00
-- url     : https://prove2.me/theorems/ac543bf2-d141-41e8-abd8-d517ae0f2f3c
-- title:
--   G: jets In lin Sub
-- statement:
--   The G construction uses the jets In lin Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Several.lean#L162-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Several.lean#L162-L166

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

theorem Formalism.L2.Th1.G.jetsIn_linSub {K : Type} [Field K] [CharZero K] {R : Subring K} {n m : Type} [Fintype n]
    [Fintype m] {A : n → m → K} (hA : ∀ i x, A i x ∈ R) {f : MvPowerSeries n K} (hf : JetsIn R f) :
    JetsIn R (linSub A f) := by sorry
