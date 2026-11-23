-- Prove2me | Theorems.Thm_Bl_general_b_fact_upper_version_goal1
-- name    : Bl.general_b_fact_upper_version.goal1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:58.712819+00:00
-- url     : https://prove2.me/theorems/b636088c-5ce0-4dd5-bdcf-120a60cff13d
-- title:
--   general b fact upper version: goal1
-- statement:
--   The general b fact upper version construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactUpperVersion/Imports.lean#L5-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactUpperVersion/Imports.lean#L5-L20

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactUpperVersion_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_upper_version

theorem Bl.general_b_fact_upper_version.goal1 :
  ∀ {R : Type} [inst : CommRing.{0} R] [IsDomain.{0} R] (ζ : R) (M : Nat) (P : Ideal.{0} R),
  Ne.{1} ζ 1 →
    Eq.{1} (HPow.hPow.{0, 0, 0} ζ M) 1 →
      Membership.mem.{0, 0} P (HSub.hSub.{0, 0, 0} ζ 1) → Membership.mem.{0, 0} P (Nat.cast.{0} M) := by sorry
