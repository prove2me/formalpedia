-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_last_goal1
-- name    : Bl.general_b_fact_right_last.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:51.212808+00:00
-- url     : https://prove2.me/theorems/aa15c02a-0816-417c-b6e1-84131f5d2989
-- title:
--   general b fact right last: goal1
-- statement:
--   The general b fact right last construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightLast/Slot.lean#L50-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightLast/Slot.lean#L50-L95

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightLast_Slot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open Bl Bl.general_b_fact_right_last

theorem Bl.general_b_fact_right_last.goal1 :
  ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [DecidableEq.{u_1 + 1} ι] {H : ι → Type u_2}
  [inst_2 : (i : ι) → NormedAddCommGroup.{u_2} (H i)] [inst_3 : (i : ι) → InnerProductSpace.{0, u_2} Complex (H i)]
  {Hs : Type u_3} [inst_4 : NormedAddCommGroup.{u_3} Hs] [inst_5 : InnerProductSpace.{0, u_3} Complex Hs]
  (tens : ((i : ι) → H i) → Hs),
  (∀ (x y : (i : ι) → H i),
      Eq.{1} (Inner.inner.{0, u_3} Complex (tens x) (tens y))
        (Finset.prod.{u_1, 0} Finset.univ.{u_1} fun (i : ι) ↦ Inner.inner.{0, u_2} Complex (x i) (y i))) →
    ∀ (M : Submodule.{0, u_3} Complex Hs),
      IsClosed.{u_3} (SetLike.coe.{u_3, u_3} M) →
        ∀ (A : (i : ι) → Set.{u_2} (H i)),
          (∀ (i : ι),
              Eq.{u_2 + 1} (Submodule.topologicalClosure.{0, u_2} (Submodule.span.{0, u_2} Complex (A i)))
                Top.top.{u_2}) →
            (∀ (x : (i : ι) → H i),
                (∀ (i : ι), Membership.mem.{u_2, u_2} (A i) (x i)) → Membership.mem.{u_3, u_3} M (tens x)) →
              ∀ (x : (i : ι) → H i), Membership.mem.{u_3, u_3} M (tens x) := by sorry
