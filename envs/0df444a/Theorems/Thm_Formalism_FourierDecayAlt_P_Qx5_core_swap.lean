-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_core_swap
-- name    : Formalism.FourierDecayAlt.P.Qx5.core_swap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:47.359079+00:00
-- url     : https://prove2.me/theorems/ccaf8b30-592c-46e1-b528-7ba36db600db
-- title:
--   Qx5: core swap
-- statement:
--   The Qx5 construction uses the core swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L864-L883
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L864-L883

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
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
variable {E : Fin n → Fin n → A} {η : Fin n → A} {x : Fin n → ℂ} {ζ : A}

theorem Formalism.FourierDecayAlt.P.Qx5.core_swap (h : CovRel E η x ζ) {t : ℕ} (a : Fin (t + 2) → Fin n) (c : Fin n) (w : ℂ)
    (M : Fin (t + 2) → Fin (t + 1) → A) (hM : ∀ p l, M (p.succAbove l) (l.predAbove p) = M p l) :
    ∑ l : Fin (t + 2), ∑ p : Fin (t + 1),
        ((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) • (Tm E w (a l) c * (η (a (l.succAbove p)) * M l p)) =
      -∑ p : Fin (t + 2), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (l : ℕ))) • (η (a p) * (Tm E (w - 1) (a (p.succAbove l)) c * M p l)) := by sorry
