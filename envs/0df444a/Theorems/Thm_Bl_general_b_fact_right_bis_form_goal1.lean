-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_bis_form_goal1
-- name    : Bl.general_b_fact_right_bis_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:34.062682+00:00
-- url     : https://prove2.me/theorems/1aae2d30-9d1e-465f-90da-cbfa9313bebb
-- title:
--   general b fact right bis form: goal1
-- statement:
--   The general b fact right bis form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightBisForm/Imports.lean#L50-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightBisForm/Imports.lean#L50-L67

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightBisForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open Bl Bl.general_b_fact_right_bis_form

theorem Bl.general_b_fact_right_bis_form.goal1 :
  ∀ {R : Type u_1} [inst : CommRing.{u_1} R] {ι : Type u_2} [inst_1 : Fintype.{u_2} ι] [DecidableEq.{u_2 + 1} ι]
  {M : ι → Type u_3} [inst_3 : (i : ι) → AddCommGroup.{u_3} (M i)] [inst_4 : (i : ι) → Module.{u_1, u_3} R (M i)]
  {A : Type u_4} [inst_5 : CommRing.{u_4} A] [inst_6 : Algebra.{u_1, u_4} R A]
  (φ : (i : ι) → LinearMap.{u_1, u_1, u_3, u_4} (RingHom.id.{u_1} R) (M i) A) (S : (i : ι) → Set.{u_3} (M i))
  (T : Submodule.{u_1, u_4} R A),
  (∀ (s : (i : ι) → M i),
      (∀ (i : ι), Membership.mem.{u_3, u_3} (S i) (s i)) →
        Membership.mem.{u_4, u_4} T
          (Finset.prod.{u_2, u_4} Finset.univ.{u_2} fun (i : ι) ↦
            DFunLike.coe.{max (u_3 + 1) (u_4 + 1), u_3 + 1, u_4 + 1} (φ i) (s i))) →
    ∀ (m : (i : ι) → M i),
      (∀ (i : ι), Membership.mem.{u_3, u_3} (Submodule.span.{u_1, u_3} R (S i)) (m i)) →
        Membership.mem.{u_4, u_4} T
          (Finset.prod.{u_2, u_4} Finset.univ.{u_2} fun (i : ι) ↦
            DFunLike.coe.{max (u_3 + 1) (u_4 + 1), u_3 + 1, u_4 + 1} (φ i) (m i)) := by sorry
