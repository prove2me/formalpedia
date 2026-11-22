-- Prove2me | Theorems.Thm_Bl_general_b_fact_second_last_goal1
-- name    : Bl.general_b_fact_second_last.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:11.193558+00:00
-- url     : https://prove2.me/theorems/de23b276-e084-427a-a65d-d4b8a605d34a
-- title:
--   general b fact second last: goal1
-- statement:
--   The general b fact second last construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondLast/Imports.lean#L5-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondLast/Imports.lean#L5-L32

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second_last

theorem Bl.general_b_fact_second_last.goal1 :
  ∀ (B : Int) {S : Nat} (c : Fin S → Int),
  (∀ (m : Fin S), LT.lt.{0} (abs.{0} (c m)) B) →
    Eq.{1} (Finset.sum.{0, 0} Finset.univ.{0} fun (m : Fin S) ↦ HMul.hMul.{0, 0, 0} (c m) (HPow.hPow.{0, 0, 0} B m.val))
        0 →
      ∀ (m : Fin S), Eq.{1} (c m) 0 := by sorry
