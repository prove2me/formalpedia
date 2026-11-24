-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_bis_other_goal1
-- name    : Bl.general_b_fact_right_bis_other.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:25.497877+00:00
-- url     : https://prove2.me/theorems/8e2ed99e-d47a-4dc8-8dd9-82ae286dcc03
-- title:
--   general b fact right bis other: goal1
-- statement:
--   The general b fact right bis other construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightBisAlt/Imports.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightBisAlt/Imports.lean#L7-L20

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightBisAlt_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_right_bis_other

theorem Bl.general_b_fact_right_bis_other.goal1 :
  ∀ {K : Type u_1} [inst : CommRing.{u_1} K] {n : Nat} {l l' : Matrix.{0, 0, u_1} (Fin n) (Fin n) K},
  (∀ (a b : Fin n), LT.lt.{0} a b → Eq.{u_1 + 1} (l a b) 0) →
    (∀ (a b : Fin n), LT.lt.{0} a b → Eq.{u_1 + 1} (l' a b) 0) →
      ∀ (a : Fin n), Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} l l' a a) (HMul.hMul.{u_1, u_1, u_1} (l a a) (l' a a)) := by sorry
