-- Prove2me | Theorems.Thm_Bl_general_b_fact_upper_bis_form_goal1
-- name    : Bl.general_b_fact_upper_bis_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:17.910009+00:00
-- url     : https://prove2.me/theorems/fa3b4fe9-e4c1-437f-ab0b-6e2c60498851
-- title:
--   general b fact upper bis form: goal1
-- statement:
--   The general b fact upper bis form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/B1959r/Imports.lean#L6-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/B1959r/Imports.lean#L6-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Mathlib
import Definitions.Def_Lemmata_B1959r_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_upper_bis_form

theorem Bl.general_b_fact_upper_bis_form.goal1 :
  ∀ {n : Nat} (f : Fin n → Rat),
  (∀ (i i' : Fin n), LT.lt.{0} i i' → LT.lt.{0} 0 (f i') → LT.lt.{0} 0 (f i)) →
    ∀ (i : Fin n), Iff (LT.lt.{0} 0 (f i)) (LT.lt.{0} i.val (PI.FJM.nP f))  := by sorry
