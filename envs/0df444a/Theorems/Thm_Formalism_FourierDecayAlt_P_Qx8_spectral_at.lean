-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_spectral_at
-- name    : Formalism.FourierDecayAlt.P.Qx8.spectral_at
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:34:04.328664+00:00
-- url     : https://prove2.me/theorems/875d38db-6a2a-4723-8750-4170eeabe326
-- title:
--   Qx8: spectral at
-- statement:
--   The Qx8 construction uses the spectral at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean#L3173-L3247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean#L3173-L3247

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

theorem Formalism.FourierDecayAlt.P.Qx8.spectral_at (hC : CapelliIdentityEntry) (hRT : RightTypeAction) (hBr : Branching)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : Set (Mx P.k P.r))
    (hPl : IsPlace P z z' π π') (hD : IsDom P.k P.r z z' (Fin.last P.r) D) (hGG : ∀ g ∈ D, GGl P.k P.r z z' g ≠ 0)
    {g : Mx P.k P.r} (hg : g ∈ Glev P.k P.r (Fin.last P.r) ∩ D) :
    ∃ S : M.Ty (P1 P) → Submodule ℂ Wq, (⨆ σ, S σ = ⊤) ∧
      (∀ J' ∈ FFl P.k P.r z z' π π' (Fin.last P.r) D, ∀ σ, ∀ v ∈ S σ, ∀ Y : ℂ,
        tL P.k P.r z z' (Fin.last P.r) Y 1 1 J' g v = ((GGl P.k P.r z z' g : ℂ) * M.xC (P1 P) σ Y) • J' g v) ∧
      (∀ J' ∈ FFl P.k P.r z z' π π' (Fin.last P.r) D, ∀ σ,
        (¬ ∃ ρ : M.Ty P, ∀ Y, M.xC P ρ Y = M.xC (P1 P) σ Y) → ∀ v ∈ S σ, J' g v = 0) := by sorry
