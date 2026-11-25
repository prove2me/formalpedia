-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_subst_mulBy_mulBy
-- name    : Formalism.L2.Th1.G.subst_mulBy_mulBy
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:09:01.796661+00:00
-- url     : https://prove2.me/theorems/f82d43e2-df59-533b-b0e3-14cdb5fef3d2
-- title:
--   G: subst mul By mul By
-- statement:
--   The G construction uses the subst mul By mul By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/InverseEndoIntegralHolds.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/InverseEndoIntegralHolds.lean#L35-L38

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.G.subst_mulBy_mulBy {l linv : PowerSeries K} (h : IsLogPair l linv) (a b : K) :
    PowerSeries.subst (mulBy l linv a) (mulBy l linv b) = mulBy l linv (b * a) := by sorry
