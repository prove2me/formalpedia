-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_le_atInfAll
-- name    : Formalism.FourierDecayAlt.P.BoxAverageLimits.le_atInfAll
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:02.814862+00:00
-- url     : https://prove2.me/theorems/86292354-8428-4a2d-8ead-595cfe14d1af
-- title:
--   Box Average Limits: le at Inf All
-- statement:
--   The Box Average Limits construction uses the le at Inf All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L352-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L352-L359

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison

theorem Formalism.FourierDecayAlt.P.BoxAverageLimits.le_atInfAll (f : ℕ) :
    (⨅ T : ℝ, 𝓟 {x : V f | ∀ v, T ≤ ‖x v‖}) ≤ atInfAll f := by sorry
