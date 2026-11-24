-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_nearestPlane_finset
-- name    : Formalism.LatticeBaseChangeAlt.nearestPlane_finset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:32.022983+00:00
-- url     : https://prove2.me/theorems/2996b320-7f19-4ef8-919e-749f9eadd825
-- title:
--   Lattice Base Change Alt: nearest Plane finset
-- statement:
--   The Lattice Base Change Alt construction uses the nearest Plane finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/ExistsSumOfMemSpanImage.lean#L59-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/ExistsSumOfMemSpanImage.lean#L59-L108

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_TransvectionIsometry
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ExistsSumOfMemSpanImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem Formalism.LatticeBaseChangeAlt.nearestPlane_finset {ι : Type*} [DecidableEq ι] (v : ι → V) (T : Finset ι) :
    ∀ x ∈ Submodule.span ℝ (v '' (T : Set ι)),
      ∃ c : ι → ℤ, ‖x - ∑ i ∈ T, (c i : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i ∈ T, ‖v i‖ ^ 2 := by sorry
