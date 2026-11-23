-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_geom
-- name    : Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.geom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:45.221549+00:00
-- url     : https://prove2.me/theorems/bb53447e-1ffd-42fb-b876-71f0754f36bf
-- title:
--   Lim: geom
-- statement:
--   The Lim construction uses the geom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L1636-L1743
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L1636-L1743

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_geom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology MeasureTheory
noncomputable section

theorem Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.geom (m : ℕ) (Kc : Set ℂ) (hK : IsCompact Kc) (h0 : (0 : ℂ) ∉ Kc) (ε : ℝ) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2))) :
    ∃ t₁ c Rz : ℝ, 0 < t₁ ∧ t₁ ≤ 1 ∧ 0 < c ∧ 1 ≤ Rz ∧ ∀ D ∈ Kc, ∀ z : ℂ, z ^ (m + 2) = (-1) ^ (m + 3) * D →
      ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ t₁ →
      z ≠ 0 ∧ ‖z‖ ≤ Rz ∧ ‖D‖ ≤ Rz ∧ c ≤ ‖z‖ ^ (m + 1) ∧
      (∀ (y : UT (m + 2) → ℂ) (τ' : ℂ), ‖y‖ ≤ 2 * ‖t‖ ^ (-ε) → ‖τ'‖ ≤ ‖t‖ →
        c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖) ∧
      (∀ y : UT (m + 2) → ℂ, ‖y‖ ≤ ‖t‖ ^ (-ε) → ‖MXY m D t (fun _ => z, y)‖ ≤ ‖t‖ ^ (-ε)) := by sorry
