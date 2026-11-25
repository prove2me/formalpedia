-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_jetsIn_toZ
-- name    : Formalism.L2.Th1.G.jetsIn_toZ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:39:20.909047+00:00
-- url     : https://prove2.me/theorems/9752d67f-4521-4291-8262-70128bec9f5d
-- title:
--   G: jets In to Z
-- statement:
--   The G construction uses the jets In to Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Several.lean#L220-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Several.lean#L220-L224

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

theorem Formalism.L2.Th1.G.jetsIn_toZ {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv : PowerSeries K}
    (h : IsLogPair l linv) (hl : IsOneUnit R (PowerSeries.derivative K l)) {n : Type} [Fintype n]
    {G : MvPowerSeries n K} (hG : IntMv R G) : JetsIn R (toZ linv G) := by sorry
