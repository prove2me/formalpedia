-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_nf_levelStart
-- name    : Formalism.FourierDecayAlt.P.Qx8.nf_levelStart
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:30:11.35739+00:00
-- url     : https://prove2.me/theorems/6bb377cb-f415-4980-9794-df6c457de909
-- title:
--   Qx8: nf level Start
-- statement:
--   The Qx8 construction uses the nf level Start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean#L499-L556
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean#L499-L556

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
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R
variable {P : M.Par} {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]

theorem Formalism.FourierDecayAlt.P.Qx8.nf_levelStart (d : NFData P 𝒜) (hR : d.Rel) (QQ : ℂ → Matrix (Fin 2) (Fin 2) 𝒜) (hQ : ∀ Y, QQ Y = d.QQ Y)
    (hS : Wd.IsStart QQ (qC P)) (hT : ∀ Y Y', Commute (QQ Y 1 0) (QQ Y' 1 0)) (l : ℕ) :
    Fr.IsLevelStart d.L (nfStart d QQ l) := by sorry
