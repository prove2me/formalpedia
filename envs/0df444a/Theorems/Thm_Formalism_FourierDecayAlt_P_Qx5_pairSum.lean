-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_pairSum
-- name    : Formalism.FourierDecayAlt.P.Qx5.pairSum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:43:50.598061+00:00
-- url     : https://prove2.me/theorems/2a1ea28d-671a-579c-8329-e35a2ab12ced
-- title:
--   Qx5: pair Sum
-- statement:
--   The Qx5 construction uses the pair Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1866-L1900
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1866-L1900

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

theorem Formalism.FourierDecayAlt.P.Qx5.pairSum (n : ℕ) (A ρ B κ : Fin n → ℂ) (G : (Fin (n - 2) → Fin n) → (Fin (n - 2) → Fin n) → X) :
    ∑ i : Fin n, ∑ j : Fin n, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * A i * B j) •
        ∑ p : Fin (n - 1), ∑ q : Fin (n - 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (skip1 i p) * κ (skip1 j q)) •
          G (skip1 i ∘ skip1 p) (skip1 j ∘ skip1 q) =
      ∑ i : Fin n, ∑ i' : Fin n, ∑ j : Fin n, ∑ j' : Fin n,
        if i < i' ∧ j < j' then
          ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (A i * ρ i' - A i' * ρ i) * (B j * κ j' - B j' * κ j)) •
            G (skip2 i i') (skip2 j j')
        else 0 := by sorry
