-- Prove2me | Theorems.Thm_Bl_general_b_fact_second_ter_goal1
-- name    : Bl.general_b_fact_second_ter.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:48.06217+00:00
-- url     : https://prove2.me/theorems/a718eeae-2ee7-4c9e-a618-7936636d1f6f
-- title:
--   general b fact second ter: goal1
-- statement:
--   The general b fact second ter construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondTer/Imports.lean#L5-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondTer/Imports.lean#L5-L30

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second_ter

theorem Bl.general_b_fact_second_ter.goal1 :
  ∀ {n : Nat} (Q : Fin n → Prop) [inst : DecidablePred.{1} Q],
  (∀ (q q' : Fin n), LE.le.{0} q' q → Q q → Q q') →
    ∀ (p : Fin n), Iff (Q p) (LT.lt.{0} p.val (Finset.card.{0} (Finset.filter.{0} Q Finset.univ.{0}))) := by sorry
