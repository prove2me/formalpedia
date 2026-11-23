-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_place_bound
-- name    : Formalism.DivisionValues.OperatorNormFrames.place_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:49.626266+00:00
-- url     : https://prove2.me/theorems/f1281a15-bf66-43ca-ae5b-89b30ddb05c7
-- title:
--   Operator Norm Frames: place bound
-- statement:
--   The Operator Norm Frames construction uses the place bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L548-L818
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L548-L818

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open OperatorNormFrames
open Formalism.DivisionValues.OperatorNormFrames

theorem Formalism.DivisionValues.OperatorNormFrames.place_bound {K : Type} [Field K] [NumberField K] [StarRing K] {n D a b : ℕ}
    (Xa : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (ha : ∀ v, IsUnit (Xa v).det)
    (Xb : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ) (hb : ∀ v, IsUnit (Xb v).det)
    (col : Matrix (Fin b) (Fin a) K)
    (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (h0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding)
    (P : Matrix (Fin D) (Fin n) K) (hP : Function.Surjective P.mulVec)
    (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hQ : IsQuotMetric P H XQ)
    (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hE : ∀ v, IsUnit (XE v).det)
    (ι : Matrix (Fin D) (Fin D) K) (hι : IsUnit ι.det)
    {Ix : Type} [Fintype Ix] (Qp : Ix → Submodule K (Fin D → K)) (hsup : (⨆ p, Qp p) = ⊤)
    (v : InfinitePlace K) (s : Ix → ℝ) (smin : ℝ) (hsmin : 0 < smin) (hs : ∀ p, smin ≤ s p)
    (hspec : ∀ p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v (ι.mulVec x) (ι.mulVec y) =
        ((s p : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XQ v x y)
    (Pt : (Fin b → K) →ₗ[K] Module.Dual K (Fin n → K))
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (hB : ∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt (col.mulVec φ) F)
    (p k : ℝ)
    (hp : Formalism.HN.opNormAt (Pi.basisFun K (Fin b)) Xb (Pi.basisFun K (Fin n)).dualBasis
      (Formalism.HN.dualFrame X0) v Pt ≤ p)
    (hk : Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) Xa (Pi.basisFun K (Fin b)) Xb v
      (Matrix.mulVecLin col) ≤ k) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) Xa (Pi.basisFun K (Fin D)).dualBasis
      (Formalism.HN.dualFrame XE) v B ≤ p * k / Real.sqrt smin := by sorry
