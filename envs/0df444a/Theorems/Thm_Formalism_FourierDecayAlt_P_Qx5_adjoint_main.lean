-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_adjoint_main
-- name    : Formalism.FourierDecayAlt.P.Qx5.adjoint_main
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:44:37.480412+00:00
-- url     : https://prove2.me/theorems/6d947d8c-afe1-40b0-a39a-e90996d7110c
-- title:
--   Qx5: adjoint main
-- statement:
--   The Qx5 construction uses the adjoint main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L748-L785
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L748-L785

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

theorem Formalism.FourierDecayAlt.P.Qx5.adjoint_main [FiniteDimensional ℂ Wp] (hH : HermHaar) (hz : inWb k r z) (hz' : inWb k r z')
    (X : ActualOps k r z z' π π') {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (Φ Ψ : RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) {K : Set (Mx k r)} (hK : IsCompact K)
    (hKD : K ⊆ Dp k r z z')
    (h0 : ∀ g ∈ Glev k r (Fin.last r), g ∉ K →
      (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 ∧ (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) (Y : ℂ) (a b : Fin 2) (v : Wq) :
    (∫ x : Mt k r, ⟪(X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
        (Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ ∂μ) =
      ∫ x : Mt k r, ⟪(Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
        (X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ ∂μ := by sorry
