-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_ae_of_haarB
-- name    : Formalism.FourierDecayAlt.P.S3dx4.ae_of_haarB
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:31:19.564281+00:00
-- url     : https://prove2.me/theorems/802ef913-4260-50b3-950e-307697ca30a2
-- title:
--   S3dx4: ae of haar B
-- statement:
--   The S3dx4 construction uses the ae of haar B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MapInvMEq.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MapInvMEq.lean#L52-L54

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

theorem Formalism.FourierDecayAlt.P.S3dx4.ae_of_haarB {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : B.IsHaarOn U μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ U := by sorry
