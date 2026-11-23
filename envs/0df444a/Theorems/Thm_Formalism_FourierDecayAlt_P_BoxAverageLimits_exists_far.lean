-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_exists_far
-- name    : Formalism.FourierDecayAlt.P.BoxAverageLimits.exists_far
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:35.502845+00:00
-- url     : https://prove2.me/theorems/11284847-0d06-419e-b7c8-4d7908e2d2a3
-- title:
--   Box Average Limits: exists far
-- statement:
--   The Box Average Limits construction uses the exists far property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L328-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L328-L350

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

theorem Formalism.FourierDecayAlt.P.BoxAverageLimits.exists_far {f : ℕ} (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La] (T : ℝ) :
    ∃ y ∈ La, ∀ v, T ≤ ‖y v‖ := by sorry
