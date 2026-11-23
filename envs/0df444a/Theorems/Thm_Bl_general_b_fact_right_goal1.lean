-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_goal1
-- name    : Bl.general_b_fact_right.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:23.295613+00:00
-- url     : https://prove2.me/theorems/8d53e649-90d1-44cb-80a4-d3ee40a4a393
-- title:
--   general b fact right: goal1
-- statement:
--   The general b fact right construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRight/Imports.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRight/Imports.lean#L7-L15

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRight_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Bl Bl.general_b_fact_right

theorem Bl.general_b_fact_right.goal1 {V ι : Type*} [AddCommGroup V] [Module ℂ V] (L : List ι) (F : ι → Module.End ℂ V)
    (c : ι → ℂ) (x : V) (hL : ∀ j ∈ L, F j x = c j • x) : (L.map F).prod x = (L.map c).prod • x := by sorry
