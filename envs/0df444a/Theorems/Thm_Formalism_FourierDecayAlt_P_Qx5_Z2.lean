-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_Z2
-- name    : Formalism.FourierDecayAlt.P.Qx5.Z2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:45:47.453032+00:00
-- url     : https://prove2.me/theorems/d9ae1d88-b28e-41e8-8b7f-dda76b642f8d
-- title:
--   Qx5: Z2
-- statement:
--   The Qx5 construction uses the Z2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1167-L1192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1167-L1192

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
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} {y : Fin n → A} {ξ : Fin n → ℂ} {ζb : A}

theorem Formalism.FourierDecayAlt.P.Qx5.Z2 (hE : GlRel E) (h : VecRel E y ξ ζb) (t : ℕ) (a b : Fin (t + 1) → Fin n) (w : ℂ) :
    qminor E a b w * ζb = ζb * qminor E a b w - ∑ p : Fin (t + 1), ∑ q : Fin (t + 1),
      ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ξ (a p)) •
        (y (b q) * qminor E (a ∘ p.succAbove) (b ∘ q.succAbove) w) := by sorry
