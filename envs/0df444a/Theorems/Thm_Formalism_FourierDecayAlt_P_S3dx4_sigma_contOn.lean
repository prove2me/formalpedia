-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_sigma_contOn
-- name    : Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:54.734775+00:00
-- url     : https://prove2.me/theorems/441ebff9-cb75-4768-abf3-7c93f00f0731
-- title:
--   S3dx4: sigma cont On
-- statement:
--   The S3dx4 construction uses the sigma cont On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SigmaContOn.lean#L49-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SigmaContOn.lean#L49-L85

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SigmaContOn
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
open scoped InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (v : H) :
    ContinuousOn (fun g => σ g v) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by sorry
