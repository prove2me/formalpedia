-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_integrable_pair
-- name    : Formalism.FourierDecayAlt.P.Qx5.integrable_pair
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:46:46.691272+00:00
-- url     : https://prove2.me/theorems/c6904907-14ef-4617-8cd7-682f8c5ebe85
-- title:
--   Qx5: integrable pair
-- statement:
--   The Qx5 construction uses the integrable pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L728-L746
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L728-L746

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
variable {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem Formalism.FourierDecayAlt.P.Qx5.integrable_pair {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (Φ Ψ : RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) {K : Set (Mx k r)} (hK : IsCompact K)
    (hKD : K ⊆ Dp k r z z') (h0 : ∀ g ∈ Glev k r (Fin.last r), g ∉ K → (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0)
    (φ : (Wq →L[ℂ] Wp) →L[ℂ] ℂ) :
    Integrable (fun x : Mt k r => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) *
      star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)))) μ ∧
    Integrable (fun x : Mt k r => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) *
      star (φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)))) μ := by sorry
