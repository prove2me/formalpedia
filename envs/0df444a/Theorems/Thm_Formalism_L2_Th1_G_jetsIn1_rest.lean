-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_jetsIn1_rest
-- name    : Formalism.L2.Th1.G.jetsIn1_rest
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:28:57.768804+00:00
-- url     : https://prove2.me/theorems/84566861-34bc-5ad1-b78a-f739994b40f4
-- title:
--   G: jets In1 rest
-- statement:
--   The G construction uses the jets In1 rest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Several.lean#L226-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Several.lean#L226-L248

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Several
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst

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

theorem Formalism.L2.Th1.G.jetsIn1_rest {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv ph : PowerSeries K}
    (h : IsLogPair l linv) (h0 : PowerSeries.constantCoeff ph = 0)
    (hj : ∀ i : ℕ, 1 ≤ i → i ≠ 2 → jet l ph i ∈ R) :
    JetsIn1 R (PowerSeries.subst linv ph - PowerSeries.C (jet l ph 2 / 2) * PowerSeries.X ^ 2) := by sorry
