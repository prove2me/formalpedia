-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_det_cell
-- name    : Formalism.FourierDecayAlt.P.Qx8.det_cell
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:29:28.75692+00:00
-- url     : https://prove2.me/theorems/60ab77be-2c58-477c-9ef9-6b93fbc26b71
-- title:
--   Qx8: det cell
-- statement:
--   The Qx8 construction uses the det cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean#L2342-L2399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean#L2342-L2399

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulIntegralStatement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Topology Formalism.YangianSpanCharacter.T
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem Formalism.FourierDecayAlt.P.Qx8.det_cell (hCS : ChainStep) (hRM : ResMem) (hFO : FamOps) (hP : TPreservesFF) (hT : TLinLoc)
    (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r) (q : ℂ → ℂ) (hdet : DetOn k r z z' π π' l.succ q)
    {D : Set (Mx k r)} (hD : IsDom k r z z' l.castSucc D) {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ FFl k r z z' π π' l.castSucc D) {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {g₁ : Mx k r} (hg₁ : g₁ ∈ Glev k r l.succ)
    (hx : w1 k r l c₀ * g₁ ∈ D) (Y : ℂ) (c d : Fin 2) :
    (tL k r z z' l.castSucc (Y + 1) 0 c (tL k r z z' l.castSucc Y 1 d J) (w1 k r l c₀ * g₁) -
      tL k r z z' l.castSucc (Y + 1) 1 c (tL k r z z' l.castSucc Y 0 d J) (w1 k r l c₀ * g₁) =
        (q Y * epsJ c d) • J (w1 k r l c₀ * g₁)) ∧
    (tL k r z z' l.castSucc Y c 0 (tL k r z z' l.castSucc (Y + 1) d 1 J) (w1 k r l c₀ * g₁) -
      tL k r z z' l.castSucc Y c 1 (tL k r z z' l.castSucc (Y + 1) d 0 J) (w1 k r l c₀ * g₁) =
        (q Y * epsJ c d) • J (w1 k r l c₀ * g₁)) := by sorry
