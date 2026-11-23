-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_version_goal1
-- name    : Bl.general_b_fact_right_version.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:10.209808+00:00
-- url     : https://prove2.me/theorems/a1d4dd8e-63d5-44ef-89b7-ecb8d83caab5
-- title:
--   general b fact right version: goal1
-- statement:
--   The general b fact right version construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightVersion/Imports.lean#L5-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightVersion/Imports.lean#L5-L23

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVersion_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_right_version

theorem Bl.general_b_fact_right_version.goal1 :
  ∀ {E Ω : Type} [inst : Field.{0} E] [inst_1 : Field.{0} Ω] [inst_2 : Algebra.{0, 0} E Ω] (σ : AlgEquiv.{0, 0, 0} E Ω Ω)
  (y : Ω),
  IsIntegral.{0, 0} E y →
    Exists.{1} fun (n : Nat) ↦ And (Ne.{1} n 0) (Eq.{1} (DFunLike.coe.{1, 1, 1} (HPow.hPow.{0, 0, 0} σ n) y) y) := by sorry
