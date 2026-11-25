-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_oneSide
-- name    : Formalism.FourierDecayAlt.P.Qx5.oneSide
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:47:54.840948+00:00
-- url     : https://prove2.me/theorems/ff95b0f7-6d74-4556-bb57-81e07d668402
-- title:
--   Qx5: one Side
-- statement:
--   The Qx5 construction uses the one Side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1847-L1864
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1847-L1864

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
variable {X : Type*} [AddCommGroup X] [Module ℂ X]

theorem Formalism.FourierDecayAlt.P.Qx5.oneSide : ∀ (n : ℕ) (α β : Fin n → ℂ) (H : (Fin (n - 2) → Fin n) → X),
    ∑ i : Fin n, ∑ p : Fin (n - 1), ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * α i * β (skip1 i p)) •
        H (skip1 i ∘ skip1 p) =
      ∑ i : Fin n, ∑ i' : Fin n,
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (α i' * β i - α i * β i')) • H (skip2 i i') else 0
  := by sorry
