-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_la_fin
-- name    : Formalism.FourierDecayAlt.P.S3dx4.la_fin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:55.68796+00:00
-- url     : https://prove2.me/theorems/5264572b-00ba-4efe-a34a-3ce773e990fc
-- title:
--   S3dx4: la fin
-- statement:
--   The S3dx4 construction uses the la fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MapInvMEq.lean#L88-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MapInvMEq.lean#L88-L133

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

theorem Formalism.FourierDecayAlt.P.S3dx4.la_fin (hNI : NormInv) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] {b : ℝ} (hb : JF.TransportedAlt k r b 0) (hb0 : b ≠ 0)
    {γ : B.Mat k r} (hγ : γ ∈ JF.Om k r D.z D.z') :
    ∫⁻ p, ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ
      ∂D.μSS < ⊤ := by sorry
