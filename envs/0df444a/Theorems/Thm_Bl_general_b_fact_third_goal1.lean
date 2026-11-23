-- Prove2me | Theorems.Thm_Bl_general_b_fact_third_goal1
-- name    : Bl.general_b_fact_third.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:37.361902+00:00
-- url     : https://prove2.me/theorems/8124ac96-e33c-4b85-8a61-88a79a7be10f
-- title:
--   general b fact third: goal1
-- statement:
--   The general b fact third construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThird/Imports.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThird/Imports.lean#L7-L32

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThird_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_third

theorem Bl.general_b_fact_third.goal1 :
  ∀ {K : Type u_1} [inst : NormedField.{u_1} K] [IsUltrametricDist.{u_1} K] (P : Polynomial.{u_1} K),
  Polynomial.Monic.{u_1} P →
    (∀ (i : Nat), LE.le.{0} (Norm.norm.{u_1} (Polynomial.coeff.{u_1} P i)) 1) →
      ∀ (x : K), Eq.{u_1 + 1} (Polynomial.eval.{u_1} x P) 0 → LE.le.{0} (Norm.norm.{u_1} x) 1 := by sorry
