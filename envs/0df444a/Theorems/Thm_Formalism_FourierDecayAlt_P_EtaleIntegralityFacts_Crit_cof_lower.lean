-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Crit_cof_lower
-- name    : Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit.cof_lower
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:52.136817+00:00
-- url     : https://prove2.me/theorems/472b7aae-f263-443f-866f-9b85ae4fd25f
-- title:
--   Crit: cof lower
-- statement:
--   The Crit construction uses the cof lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L1361-L1390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L1361-L1390

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology

theorem Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit.cof_lower (m : ℕ) {δ c ε : ℝ} (hδ : 0 < δ) (hc : 2 ≤ c) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2))) {t : ℂ} (ht0 : t ≠ 0) (ht1 : ‖t‖ ≤ 1)
    (hts : ((m : ℝ) + 1) ^ (m + 1) * c ^ m * Real.sqrt ‖t‖ ≤ δ ^ (m + 1) / 2)
    (p : XY m) (hx : ∀ k, ‖p.1 k‖ ≤ c) (hxl : ∀ k, δ ≤ ‖p.1 k‖) (hy : ‖p.2‖ ≤ 2 * ‖t‖ ^ (-ε)) :
    δ ^ (m + 1) ≤ ‖∏ k, p.1 k‖ ∧ δ ^ (m + 1) / 2 ≤ ‖cofXY m t p‖ := by sorry
