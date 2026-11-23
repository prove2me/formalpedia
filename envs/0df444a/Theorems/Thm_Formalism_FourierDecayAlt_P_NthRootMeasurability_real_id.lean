-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_real_id
-- name    : Formalism.FourierDecayAlt.P.NthRootMeasurability.real_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:55.641935+00:00
-- url     : https://prove2.me/theorems/7eefa5e5-2cd6-47c0-92d7-0a66e6355609
-- title:
--   Nth Root Measurability: real id
-- statement:
--   The Nth Root Measurability construction uses the real id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L122-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean#L122-L141

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

theorem Formalism.FourierDecayAlt.P.NthRootMeasurability.real_id (s M : ℕ) (hs : 1 ≤ s) (hM : 2 ≤ M) (t z : ℂ) (ht : t ≠ 0) (hz : z ≠ 0) :
    ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 *
      (‖t‖ ^ (2 * (s - 1) * (M + s - 2)) *
        ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * z ^ s‖ ^ (2 * (M - 2)) /
          (‖t‖ ^ (2 * (s - 1) ^ 2) * (s : ℝ) ^ 2)) * ‖z‖ ^ (2 * (s - 1) ^ 2) =
      ‖z‖ ^ (2 * s * (M + s - 3)) := by sorry
