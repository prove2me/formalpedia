-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_proj_exists
-- name    : Formalism.FourierDecayAlt.P.Qx8.proj_exists
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:32:31.363803+00:00
-- url     : https://prove2.me/theorems/963df083-93af-4d98-a3c7-4c5c16235551
-- title:
--   Qx8: proj exists
-- statement:
--   The Qx8 construction uses the proj exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean#L3317-L3380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean#L3317-L3380

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
open Formalism.FourierDecayAlt.M
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.Qx8.proj_exists (hP : TPreservesFF) (P : M.Par) (hOK : P.OK) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (hz : inWb P.k P.r z) (hz' : inWb P.k P.r z')
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : Set (Mx P.k P.r))
    (hD : IsDom P.k P.r z z' (Fin.last P.r) D) (hGG : ∀ g ∈ D, GGl P.k P.r z z' g ≠ 0)
    (S : ∀ g, g ∈ Glev P.k P.r (Fin.last P.r) ∩ D → M.Ty (P1 P) → Submodule ℂ Wq)
    (hS : ∀ g hg, ∀ J' ∈ FFl P.k P.r z z' π π' (Fin.last P.r) D, ∀ σ, ∀ v ∈ S g hg σ, ∀ Y : ℂ,
        tL P.k P.r z z' (Fin.last P.r) Y 1 1 J' g v = ((GGl P.k P.r z z' g : ℂ) * M.xC (P1 P) σ Y) • J' g v)
    {J : Mx P.k P.r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl P.k P.r z z' π π' (Fin.last P.r) D) (σ₀ : M.Ty (P1 P)) :
    ∃ K ∈ FFl P.k P.r z z' π π' (Fin.last P.r) D, ∀ g hg, ∀ σ', ∀ v ∈ S g hg σ',
      K g v = (if σ' = σ₀ then (1 : ℂ) else 0) • J g v := by sorry
