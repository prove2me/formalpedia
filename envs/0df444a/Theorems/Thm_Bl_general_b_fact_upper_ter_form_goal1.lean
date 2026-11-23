-- Prove2me | Theorems.Thm_Bl_general_b_fact_upper_ter_form_goal1
-- name    : Bl.general_b_fact_upper_ter_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:37.563745+00:00
-- url     : https://prove2.me/theorems/18d7abc6-26e4-4c67-b8eb-b6b2772a82d8
-- title:
--   general b fact upper ter form: goal1
-- statement:
--   The general b fact upper ter form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactUpperTerForm/Imports.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactUpperTerForm/Imports.lean#L16-L22

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_upper_ter_form

theorem Bl.general_b_fact_upper_ter_form.goal1 :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {ι : Type} (s : Finset.{0} ι) (g : ι → PadicAlgCl p) {C : Real},
  LE.le.{0} 0 C →
    (∀ (j : ι), Membership.mem.{0, 0} s j → LE.le.{0} (Norm.norm.{0} (g j)) C) →
      LE.le.{0} (Norm.norm.{0} (Finset.sum.{0, 0} s fun (j : ι) ↦ g j)) C := by sorry
