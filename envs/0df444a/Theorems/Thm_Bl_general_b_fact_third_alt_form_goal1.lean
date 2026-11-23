-- Prove2me | Theorems.Thm_Bl_general_b_fact_third_alt_form_goal1
-- name    : Bl.general_b_fact_third_alt_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:01.083882+00:00
-- url     : https://prove2.me/theorems/a6285f19-ad03-4dbb-8c18-5f5f2014b819
-- title:
--   general b fact third alt form: goal1
-- statement:
--   The general b fact third alt form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdAltForm/Imports.lean#L5-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdAltForm/Imports.lean#L5-L35

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdAltForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_alt_form

theorem Bl.general_b_fact_third_alt_form.goal1 :
  ∀ {E : Type} [inst : CommRing.{0} E] {O : Subring.{0} E} {V : Type} [inst_1 : AddCommGroup.{0} V]
  [inst_2 : Module.{0, 0} E V] {ι : Type} [inst_3 : Fintype.{0} ι] [inst_4 : DecidableEq.{1} ι] (g b : ι → V),
  LinearIndependent.{0, 0, 0} (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x) g →
    Eq.{1} (Submodule.span.{0, 0} (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x) (Set.range.{0, 1} g))
        (Submodule.span.{0, 0} (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x) (Set.range.{0, 1} b)) →
      Exists.{1} fun (Q : Matrix.{0, 0, 0} ι ι (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x)) ↦
        Exists.{1} fun (P : Matrix.{0, 0, 0} ι ι (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x)) ↦
          And
            (∀ (j : ι),
              Eq.{1} (g j) (Finset.sum.{0, 0} Finset.univ.{0} fun (i : ι) ↦ HSMul.hSMul.{0, 0, 0} (Q i j) (b i)))
            (Eq.{1} (HMul.hMul.{0, 0, 0} P Q) 1) := by sorry
