-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_oneSide_succ
-- name    : Formalism.FourierDecayAlt.P.Qx5.oneSide_succ
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:47:07.429246+00:00
-- url     : https://prove2.me/theorems/93babb67-966d-5f2f-9200-e549b1c4e298
-- title:
--   Qx5: one Side succ
-- statement:
--   The Qx5 construction uses the one Side succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1811-L1845
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1811-L1845

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

theorem Formalism.FourierDecayAlt.P.Qx5.oneSide_succ (M : ℕ) (α β : Fin (M + 2) → ℂ) (H : (Fin M → Fin (M + 2)) → X) :
    ∑ i : Fin (M + 2), ∑ p : Fin (M + 1), ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * α i * β (i.succAbove p)) •
        H (i.succAbove ∘ p.succAbove) =
      ∑ i : Fin (M + 2), ∑ i' : Fin (M + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (α i' * β i - α i * β i')) • H (skip2 i i') else 0 := by sorry
