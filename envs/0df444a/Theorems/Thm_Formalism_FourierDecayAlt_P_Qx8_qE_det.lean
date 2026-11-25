-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_qE_det
-- name    : Formalism.FourierDecayAlt.P.Qx8.qE_det
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:40:04.375412+00:00
-- url     : https://prove2.me/theorems/852a0f0b-0076-4bf2-be55-bb7b05999623
-- title:
--   Qx8: q E det
-- statement:
--   The Qx8 construction uses the q E det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean#L2099-L2133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean#L2099-L2133

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
  {i : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}

theorem Formalism.FourierDecayAlt.P.Qx8.qE_det (C : FamCtx k r z z' i Dc) (hP : TPreservesFF) (hT : TLinLoc) (q : ℂ → ℂ)
    (hdet : ∀ D, IsDom k r z z' i D → ∀ J ∈ FFl k r z z' π π' i D, ∀ g ∈ Glev k r i ∩ D, ∀ (Y : ℂ) (c d : Fin 2),
      (tL k r z z' i (Y + 1) 0 c (tL k r z z' i Y 1 d J) g -
          tL k r z z' i (Y + 1) 1 c (tL k r z z' i Y 0 d J) g = (q Y * epsJ c d) • J g) ∧
      (tL k r z z' i Y c 0 (tL k r z z' i (Y + 1) d 1 J) g -
          tL k r z z' i Y c 1 (tL k r z z' i (Y + 1) d 0 J) g = (q Y * epsJ c d) • J g)) :
    W.IsDet (fun Y => Matrix.of (qE (π := π) (π' := π') C hP hT Y)) q := by sorry
