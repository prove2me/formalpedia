-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_core
-- name    : Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:35.72197+00:00
-- url     : https://prove2.me/theorems/b81d7a08-67d9-404d-bc7c-781f1534f6bb
-- title:
--   Etale Integrality Facts: core
-- statement:
--   The Etale Integrality Facts construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L973-L983
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L973-L983

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
open Formalism.FourierDecayAlt.G Matrix Filter Topology
noncomputable section

theorem Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.core : ∃ a b : ℕ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m q : ℕ) (β D : ℂ) (tt : E → ℂ)
    (xx : E → Fin (m + 1) → ℂ) (yy : E → UT (m + 2) → ℂ) (u : E) (Q W : ℝ),
    2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial ≤ Q → DB q tt u Q 1 → (∀ k, DB q (fun v => xx v k) u Q 1) →
    (∀ e, DB q (fun v => yy v e) u Q 1) → ‖D‖ ≤ Q → ‖β‖ ≤ Q → Q ^ (4 * (m + 2)) ≤ W →
    cofXY m (tt u) (xx u, yy u) ≠ 0 → ‖cofXY m (tt u) (xx u, yy u)‖⁻¹ ≤ W →
    ∏ k, xx u k ≠ 0 → ‖∏ k, xx u k‖⁻¹ ≤ W →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Φ : Mat (m + 1 + 1) → V) (K' : ℝ),
      DB q Φ (MXY m D (tt u) (xx u, yy u)) K' 1 →
      DB q (fun v => ampE β m Φ D (tt v) (xx v, yy v)) u (K' * W ^ a) (W ^ b) := by sorry
