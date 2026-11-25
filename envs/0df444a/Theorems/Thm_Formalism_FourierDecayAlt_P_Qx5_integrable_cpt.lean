-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_integrable_cpt
-- name    : Formalism.FourierDecayAlt.P.Qx5.integrable_cpt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:47:03.224816+00:00
-- url     : https://prove2.me/theorems/d5af3d69-9cd6-4471-8579-7adb308d0224
-- title:
--   Qx5: integrable cpt
-- statement:
--   The Qx5 construction uses the integrable cpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L681-L692
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L681-L692

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
open Qx2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.Qx5.integrable_cpt {i : Fin (r + 1)} {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r i) μ) {D K : Set (Mx k r)}
    {p : Mx k r → ℂ} (hK : IsCompact K) (hKD : K ⊆ D) (hp : ContinuousOn p (Glev k r i ∩ D))
    (h0 : ∀ g ∈ Glev k r i, g ∉ K → p g = 0) : Integrable (fun x : Mt k r => p (Matrix.of x)) μ := by sorry
