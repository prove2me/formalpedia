-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_remainder_norm_le
-- name    : Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.remainder_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:23.990429+00:00
-- url     : https://prove2.me/theorems/2b68d065-6b1d-41f7-8569-d1b61cec82d9
-- title:
--   Etale Integrality Facts: remainder norm le
-- statement:
--   The Etale Integrality Facts construction uses the remainder norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L517-L555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L517-L555

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix
noncomputable section

theorem Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.remainder_norm_le (m : ℕ) (t : ℂ) (p : XY m) {R : ℝ} (hR : 1 ≤ R) (ht : ‖t‖ ≤ 1) (hx : ∀ k, ‖p.1 k‖ ≤ R)
    (hy : ‖p.2‖ ≤ R) : ‖r1XY m t p‖ ≤ ((m : ℝ) + 1) ^ (m + 2) * R ^ (m + 1) := by sorry
