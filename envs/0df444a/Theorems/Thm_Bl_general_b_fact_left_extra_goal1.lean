-- Prove2me | Theorems.Thm_Bl_general_b_fact_left_extra_goal1
-- name    : Bl.general_b_fact_left_extra.goal1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:23.908136+00:00
-- url     : https://prove2.me/theorems/01566de8-0133-47b9-92d1-a59bd333f42a
-- title:
--   general b fact left extra: goal1
-- statement:
--   The general b fact left extra construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftExtra/Imports.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftExtra/Imports.lean#L9-L18

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftExtra_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open Bl Bl.general_b_fact_left_extra
variable {K : Type*} [Field K] [NumberField K]

theorem Bl.general_b_fact_left_extra.goal1 {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ t, w (a i) ≤ M) : w (∑ i ∈ t, a i) ≤ M := by sorry
