-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_mid_id
-- name    : Formalism.FourierDecayAlt.P.Qx5.mid_id
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:56:56.461558+00:00
-- url     : https://prove2.me/theorems/17539152-1ea7-41c6-a2b2-fbffe0938071
-- title:
--   Qx5: mid id
-- statement:
--   The Qx5 construction uses the mid id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1026-L1029
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1026-L1029

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem Formalism.FourierDecayAlt.P.Qx5.mid_id (E : Fin n → Fin n → A) (x y : ℂ) (p c q d : Fin n) :
    Tm E x p c * Tm E y q d - Tm E y p c * Tm E x q d + Tm E x q d * Tm E y p c - Tm E y q d * Tm E x p c = 0 := by sorry
