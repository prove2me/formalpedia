-- Prove2me | Theorems.Thm_Bl_general_b_fact_left_more_goal1
-- name    : Bl.general_b_fact_left_more.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:56.411782+00:00
-- url     : https://prove2.me/theorems/f1ff8db6-3535-45bb-a7f8-5c45b5d05436
-- title:
--   general b fact left more: goal1
-- statement:
--   The general b fact left more construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftMore/Imports.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftMore/Imports.lean#L9-L24

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial IsLocalRing
open Bl Bl.general_b_fact_left_more
variable {n : ℕ}

theorem Bl.general_b_fact_left_more.goal1 (p : Fin n → ℂ) (a : MvPolynomial (Fin n) ℂ) :
    a - C (eval p a) ∈ Ideal.span (Set.range fun i => X i - C (p i)) := by sorry
