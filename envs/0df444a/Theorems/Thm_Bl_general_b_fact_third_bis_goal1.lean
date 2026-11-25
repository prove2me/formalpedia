-- Prove2me | Theorems.Thm_Bl_general_b_fact_third_bis_goal1
-- name    : Bl.general_b_fact_third_bis.goal1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:03.187261+00:00
-- url     : https://prove2.me/theorems/956f2c61-c1b2-537e-b7bd-c7ef1f8a4648
-- title:
--   general b fact third bis: goal1
-- statement:
--   The general b fact third bis construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdBis/Imports.lean#L7-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdBis/Imports.lean#L7-L66

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdBis_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_third_bis

theorem Bl.general_b_fact_third_bis.goal1 :
  ∀ {E : Type u_1} [inst : Field.{u_1} E] [NumberField.{u_1} E] (φ : RingHom.{u_1, 0} E Complex) {n : Nat}
  (L : Submodule.{u_1, u_1} (NumberField.RingOfIntegers.{u_1} E) (Fin n → E)),
  Submodule.FG.{u_1, u_1} L →
    Eq.{u_1 + 1} (Submodule.span.{u_1, u_1} E (SetLike.coe.{u_1, u_1} L)) Top.top.{u_1} →
      ∀ (M : Matrix.{0, 0, u_1} (Fin n) (Fin n) E),
        (∀ (x : Fin n → E),
            Membership.mem.{u_1, u_1} L x → Membership.mem.{u_1, u_1} L (Matrix.mulVec.{u_1, 0, 0} M x)) →
          IsIntegral.{0, u_1} Int (Matrix.trace.{0, u_1} M) := by sorry
