-- Prove2me | Theorems.Thm_Bl_general_b_fact_upper_alt_form_goal1
-- name    : Bl.general_b_fact_upper_alt_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:25.089664+00:00
-- url     : https://prove2.me/theorems/8f20e4b1-113a-4112-8f75-7b331d3f5c49
-- title:
--   general b fact upper alt form: goal1
-- statement:
--   The general b fact upper alt form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactUpperAltForm/Imports.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactUpperAltForm/Imports.lean#L5-L21

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactUpperAltForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_upper_alt_form

theorem Bl.general_b_fact_upper_alt_form.goal1 :
  ∀ {K : Type} [inst : Field.{0} K] {n k : Type} [Fintype.{0} n] [DecidableEq.{1} n] [inst_3 : Fintype.{0} k]
  [DecidableEq.{1} k] (f : RingHom.{0, 0} K Complex) (A : Matrix.{0, 0, 0} n k K),
  Function.Injective.{1, 1} (Matrix.mulVec.{0, 0, 0} A) →
    Function.Injective.{1, 1} (Matrix.mulVec.{0, 0, 0} (Matrix.map.{0, 0, 0, 0} A (DFunLike.coe.{1, 1, 1} f))) := by sorry
