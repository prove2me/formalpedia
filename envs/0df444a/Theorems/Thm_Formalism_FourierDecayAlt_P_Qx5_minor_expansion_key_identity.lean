-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_minor_expansion_key_identity
-- name    : Formalism.FourierDecayAlt.P.Qx5.minor_expansion_key_identity
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:47:32.818288+00:00
-- url     : https://prove2.me/theorems/be2ada55-8733-40fa-9ae2-42026b8c67c2
-- title:
--   Qx5: minor expansion key identity
-- statement:
--   The Qx5 construction uses the minor expansion key identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L896-L933
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L896-L933

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ

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
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} {η : Fin n → A} {x : Fin n → ℂ} {ζ : A}

theorem Formalism.FourierDecayAlt.P.Qx5.minor_expansion_key_identity (h : CovRel E η x ζ) {t : ℕ} (a b : Fin (t + 2) → Fin n) (w : ℂ) (q : Fin (t + 1)) :
    ∑ l : Fin (t + 2), ((-1 : ℂ) ^ (l : ℕ)) • (Tm E w (a l) (b 0) *
        ∑ p : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * x ((b ∘ Fin.succ) q)) •
          (η ((a ∘ l.succAbove) p) * qminor E ((a ∘ l.succAbove) ∘ p.succAbove) ((b ∘ Fin.succ) ∘ q.succAbove) (w - 1 - 1))) =
      ∑ p : Fin (t + 2), ((-1 : ℂ) ^ ((p : ℕ) + (q.succ : ℕ)) * x (b q.succ)) •
        (η (a p) * qminor E (a ∘ p.succAbove) (b ∘ q.succ.succAbove) (w - 1)) := by sorry
