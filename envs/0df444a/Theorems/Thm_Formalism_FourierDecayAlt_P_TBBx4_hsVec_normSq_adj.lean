-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx4_hsVec_normSq_adj
-- name    : Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:56:53.413002+00:00
-- url     : https://prove2.me/theorems/ae7ad135-bf2c-4a24-ba0e-eb198c5ccc09
-- title:
--   TBBx4: hs Vec norm Sq adj
-- statement:
--   The TBBx4 construction uses the hs Vec norm Sq adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L22-L34

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularityAtPlaceOfSubadditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx4
open MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal ComplexConjugate
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (Y : Wq →L[ℂ] Wp) :
    ‖B.hsVec Y‖ ^ 2 = ∑ j, ‖(ContinuousLinearMap.adjoint Y) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 := by sorry
