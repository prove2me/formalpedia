-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_dP_four
-- name    : Formalism.FourierDecayAlt.P.Qx5.dP_four
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:45:43.943828+00:00
-- url     : https://prove2.me/theorems/86ae1ba7-b226-4cc1-ae20-bd5e5279e0a3
-- title:
--   Qx5: d P four
-- statement:
--   The Qx5 construction uses the d P four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1031-L1052
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1031-L1052

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
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem Formalism.FourierDecayAlt.P.Qx5.dP_four (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (θ : Fin (m + 1) → ℂ) (i : Fin m)
    (σ τ : Equiv.Perm (Fin (m + 1))) :
    dP E a b θ σ τ - dP E a b (θ ∘ Equiv.swap i.castSucc i.succ) σ τ
      + dP E a b θ (σ * Equiv.swap i.castSucc i.succ) (τ * Equiv.swap i.castSucc i.succ)
      - dP E a b (θ ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ)
          (τ * Equiv.swap i.castSucc i.succ) = 0 := by sorry
