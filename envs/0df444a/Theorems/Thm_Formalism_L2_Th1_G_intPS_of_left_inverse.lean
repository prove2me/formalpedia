-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_intPS_of_left_inverse
-- name    : Formalism.L2.Th1.G.intPS_of_left_inverse
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:09:25.563186+00:00
-- url     : https://prove2.me/theorems/a254fe1d-96b6-5643-a19b-64a8a9c6bfea
-- title:
--   G: int PS of left inverse
-- statement:
--   The G construction uses the int PS of left inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/InverseEndoIntegralHolds.lean#L44-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/InverseEndoIntegralHolds.lean#L44-L82

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

theorem Formalism.L2.Th1.G.intPS_of_left_inverse (R : Subring K) {f g : PowerSeries K} (hf : IntPS R f)
    (hf0 : PowerSeries.constantCoeff f = 0) (hu : (PowerSeries.coeff 1 f)⁻¹ ∈ R)
    (hne : PowerSeries.coeff 1 f ≠ 0) (hg : PowerSeries.subst f g = PowerSeries.X) : IntPS R g := by sorry
