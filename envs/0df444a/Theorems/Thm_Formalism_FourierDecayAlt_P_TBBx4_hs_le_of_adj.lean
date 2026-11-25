-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx4_hs_le_of_adj
-- name    : Formalism.FourierDecayAlt.P.TBBx4.hs_le_of_adj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:01:01.616545+00:00
-- url     : https://prove2.me/theorems/f1fa163c-7d7b-4b6c-b1e3-3ea1247eb7ba
-- title:
--   TBBx4: hs le of adj
-- statement:
--   The TBBx4 construction uses the hs le of adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L36-L43

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

theorem Formalism.FourierDecayAlt.P.TBBx4.hs_le_of_adj (X : Wq →L[ℂ] Wp) (A A' : Wq →L[ℂ] Wq) (K : ℝ)
    (h : ∀ v : Wq, ‖v‖ ^ 2 ≤
      K * (‖(ContinuousLinearMap.adjoint A) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint A') v‖ ^ 2)) :
    ‖B.hsVec X‖ ^ 2 ≤ K * (‖B.hsVec (X.comp A)‖ ^ 2 + ‖B.hsVec (X.comp A')‖ ^ 2) := by sorry
