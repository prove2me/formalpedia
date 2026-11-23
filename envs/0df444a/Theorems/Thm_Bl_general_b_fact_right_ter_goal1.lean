-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_ter_goal1
-- name    : Bl.general_b_fact_right_ter.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:44.362958+00:00
-- url     : https://prove2.me/theorems/f89b5e2c-9814-4556-80ba-807e141eb4b1
-- title:
--   general b fact right ter: goal1
-- statement:
--   The general b fact right ter construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightTer/Imports.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightTer/Imports.lean#L7-L15

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightTer_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix TensorProduct NumberField IsDedekindDomain
open Bl Bl.general_b_fact_right_ter

theorem Bl.general_b_fact_right_ter.goal1 {F : Type} [Field F] [NumberField F] {ι : Type} (s : Finset ι)
    (Q : ι → 𝓞 F → Prop) (hQ : ∀ i c r, Q i c → Q i (c * r)) (h : ∀ i ∈ s, ∃ c, c ≠ 0 ∧ Q i c) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i ∈ s, Q i c := by sorry
