-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_map_smul_muPi
-- name    : Formalism.FourierDecayAlt.P.G5.map_smul_muPi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:00:04.233811+00:00
-- url     : https://prove2.me/theorems/0bdefdcf-1702-439e-8e1b-d8457763f08f
-- title:
--   G5: map smul mu Pi
-- statement:
--   The G5 construction uses the map smul mu Pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L50-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L50-L66

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G5.map_smul_muPi (β z : ℂ) (ι : Type) [Fintype ι] (hz : z ≠ 0) :
    Measure.map (fun v : ι → ℂ => z • v) (muPi β ι) =
      Real.toNNReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) • muPi β ι := by sorry
