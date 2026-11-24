-- Prove2me | Theorems.Thm_Bl_general_b_fact_left_ter_goal1
-- name    : Bl.general_b_fact_left_ter.goal1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:20:59.050292+00:00
-- url     : https://prove2.me/theorems/3c79ccee-7afc-4b6f-8152-38f9448ac208
-- title:
--   general b fact left ter: goal1
-- statement:
--   The general b fact left ter construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftTer/Imports.lean#L7-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftTer/Imports.lean#L7-L30

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftTer_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_left_ter

theorem Bl.general_b_fact_left_ter.goal1 :
  ∀ {F : Type u_1} [inst : NormedField.{u_1} F] [IsUltrametricDist.{u_1} F] {y : F} (p : Polynomial.{0} Int),
  Polynomial.Monic.{0} p →
    Eq.{u_1 + 1} (Polynomial.eval₂.{0, u_1} (Int.castRingHom.{u_1} F) y p) 0 → LE.le.{0} (Norm.norm.{u_1} y) 1 := by sorry
