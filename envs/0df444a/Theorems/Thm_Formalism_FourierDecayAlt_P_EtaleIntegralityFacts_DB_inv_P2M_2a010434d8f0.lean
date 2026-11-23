-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_inv_P2M_2a010434d8f0
-- name    : Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.DB_inv_P2M_2a010434d8f0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:26.159795+00:00
-- url     : https://prove2.me/theorems/4d1f2cfe-38f9-404b-a70f-326af0a7cf5b
-- title:
--   Etale Integrality Facts: DB inv P2 M 2a010434d8f0
-- statement:
--   The Etale Integrality Facts construction uses the DB inv P2 M 2a010434d8f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L214-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L214-L227

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
open Filter Topology
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.DB_inv_P2M_2a010434d8f0 (q : ℕ) (c : ℂ) (hc : c ≠ 0) :
    DB q (fun z : ℂ => z⁻¹) c (q.factorial * ‖c‖⁻¹) ‖c‖⁻¹ := by sorry

alias «Formalism».«FourierDecayAlt».«P».«EtaleIntegralityFacts».«DB_inv» := Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.DB_inv_P2M_2a010434d8f0
