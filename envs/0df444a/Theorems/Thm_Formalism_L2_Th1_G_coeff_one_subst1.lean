-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_coeff_one_subst1
-- name    : Formalism.L2.Th1.G.coeff_one_subst1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:40:28.124977+00:00
-- url     : https://prove2.me/theorems/36b8fa49-bd27-4f86-b5b9-56394b46979b
-- title:
--   G: coeff one subst1
-- statement:
--   The G construction uses the coeff one subst1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/InverseEndoIntegralHolds.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/InverseEndoIntegralHolds.lean#L18-L27

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

theorem Formalism.L2.Th1.G.coeff_one_subst1 (g : PowerSeries K) {a : PowerSeries K}
    (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst a g : PowerSeries K) =
      PowerSeries.coeff 1 g * PowerSeries.coeff 1 a := by sorry
