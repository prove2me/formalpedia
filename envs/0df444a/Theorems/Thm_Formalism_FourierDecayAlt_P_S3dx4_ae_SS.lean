-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_ae_SS
-- name    : Formalism.FourierDecayAlt.P.S3dx4.ae_SS
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:02.822991+00:00
-- url     : https://prove2.me/theorems/54795b27-2f15-450c-8e0e-4e530a8912a6
-- title:
--   S3dx4: ae SS
-- statement:
--   The S3dx4 construction uses the ae SS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MapInvMEq.lean#L56-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MapInvMEq.lean#L56-L73

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.S3dx4.ae_SS {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] :
    ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z ∧ Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r ∧
      Matrix.of p.2.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z' ∧ Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r := by sorry
