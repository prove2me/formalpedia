-- Prove2me | Theorems.Thm_Bl_general_b_fact_more_goal1
-- name    : Bl.general_b_fact_more.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:56.549169+00:00
-- url     : https://prove2.me/theorems/45dc2665-9b4f-44b2-be05-bb5090e112c3
-- title:
--   general b fact more: goal1
-- statement:
--   The general b fact more construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactMore/Imports.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactMore/Imports.lean#L29-L45

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_2 u_3
open Bl Bl.general_b_fact_more

theorem Bl.general_b_fact_more.goal1 :
  ∀ {R : Type u_2} {ι : Type u_3} [inst : CommRing.{u_2} R] (s : Finset.{u_3} ι) (p : ι → Polynomial.{u_2} R)
  (e : ι → Nat),
  (∀ (i : ι), LE.le.{0} (Polynomial.natDegree.{u_2} (p i)) 1) →
    And
      (LE.le.{0}
        (Polynomial.natDegree.{u_2} (Finset.prod.{u_3, u_2} s fun (i : ι) ↦ HPow.hPow.{u_2, 0, u_2} (p i) (e i)))
        (Finset.sum.{u_3, 0} s fun (i : ι) ↦ e i))
      (Eq.{u_2 + 1}
        (Polynomial.coeff.{u_2} (Finset.prod.{u_3, u_2} s fun (i : ι) ↦ HPow.hPow.{u_2, 0, u_2} (p i) (e i))
          (Finset.sum.{u_3, 0} s fun (i : ι) ↦ e i))
        (Finset.prod.{u_3, u_2} s fun (i : ι) ↦ HPow.hPow.{u_2, 0, u_2} (Polynomial.coeff.{u_2} (p i) 1) (e i))) := by sorry
