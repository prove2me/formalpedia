-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_variant_goal1
-- name    : Bl.general_b_fact_right_variant.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:45.713637+00:00
-- url     : https://prove2.me/theorems/a2e2cdd3-1db8-4bc8-a11f-081cd4a3ab4e
-- title:
--   general b fact right variant: goal1
-- statement:
--   The general b fact right variant construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightVariant/Imports.lean#L7-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightVariant/Imports.lean#L7-L35

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVariant_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_right_variant

theorem Bl.general_b_fact_right_variant.goal1 :
  ∀ {R : Type u_1} [inst : CommRing.{u_1} R] (P : Ideal.{u_1} R) [hP : Ideal.IsPrime.{u_1} P] (n : Nat),
  Ne.{1} n 0 →
    Membership.mem.{u_1, u_1} P (Nat.cast.{u_1} n) →
      Exists.{1} fun (p : Nat) ↦
        And (Nat.Prime p) (And (Dvd.dvd.{0} p n) (Membership.mem.{u_1, u_1} P (Nat.cast.{u_1} p))) := by sorry
