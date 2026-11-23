-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_core
-- name    : Formalism.FourierDecayAlt.P.NthRootMeasurability.core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:25.006502+00:00
-- url     : https://prove2.me/theorems/1b00dab3-2604-4865-b9ad-3fdef0404ad7
-- title:
--   Nth Root Measurability: core
-- statement:
--   The Nth Root Measurability construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L95-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L95-L120

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NthRootMeasurability
open Formalism.FourierDecayAlt.crystallineComparison

theorem Formalism.FourierDecayAlt.P.NthRootMeasurability.core (s : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) (H : ℂ → ENNReal) (hH : Measurable H) :
    ∫⁻ c, ((nthRoots s (u * c)).map H).sum =
      ∫⁻ z, ENNReal.ofReal (‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2) * H z := by sorry
