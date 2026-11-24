-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_exists_orth_split
-- name    : Formalism.LatticeBaseChangeAlt.exists_orth_split
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:51:46.541382+00:00
-- url     : https://prove2.me/theorems/bf791a7c-60e9-4854-8ea0-6154d55e64db
-- title:
--   Lattice Base Change Alt: exists orth split
-- statement:
--   The Lattice Base Change Alt construction uses the exists orth split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/ExistsSumOfMemSpanImage.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/ExistsSumOfMemSpanImage.lean#L21-L31

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

theorem Formalism.LatticeBaseChangeAlt.exists_orth_split {ι : Type*} (v : ι → V) (T : Finset ι) (a : V) :
    ∃ w ∈ Submodule.span ℝ (v '' (T : Set ι)), ∃ z : V,
      (∀ p ∈ Submodule.span ℝ (v '' (T : Set ι)), inner ℝ p z = 0) ∧ a = w + z ∧
        ‖z‖ ^ 2 ≤ ‖a‖ ^ 2 := by sorry
