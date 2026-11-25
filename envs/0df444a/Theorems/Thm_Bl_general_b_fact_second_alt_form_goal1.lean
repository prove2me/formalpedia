-- Prove2me | Theorems.Thm_Bl_general_b_fact_second_alt_form_goal1
-- name    : Bl.general_b_fact_second_alt_form.goal1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:16:23.929341+00:00
-- url     : https://prove2.me/theorems/0ec7b6a2-105a-4df1-839a-96d4b915dba3
-- title:
--   general b fact second alt form: goal1
-- statement:
--   The general b fact second alt form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondAltForm/Imports.lean#L7-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondAltForm/Imports.lean#L7-L147

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondAltForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact_second_alt_form

theorem Bl.general_b_fact_second_alt_form.goal1 :
  ∀ {Wq : Type u_1} {Wp : Type u_2} [inst : AddCommGroup.{u_1} Wq] [inst_1 : Module.{0, u_1} Complex Wq]
  [FiniteDimensional.{0, u_1} Complex Wq] [inst_3 : AddCommGroup.{u_2} Wp] [inst_4 : Module.{0, u_2} Complex Wp]
  [FiniteDimensional.{0, u_2} Complex Wp] (S' : Submodule.{0, u_1} Complex Wq) (S : Submodule.{0, u_2} Complex Wp)
  (Gq : Set.{u_1} (Module.End.{0, u_1} Complex Wq)) (Gp : Set.{u_2} (Module.End.{0, u_2} Complex Wp)),
  (∀ (K : Submodule.{0, u_1} Complex Wq),
      LE.le.{u_1} K S' →
        (∀ (A : Module.End.{0, u_1} Complex Wq),
            Membership.mem.{u_1, u_1} Gq A →
              ∀ (v : Wq),
                Membership.mem.{u_1, u_1} K v →
                  Membership.mem.{u_1, u_1} K (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} A v)) →
          Or (Eq.{u_1 + 1} K Bot.bot.{u_1}) (Eq.{u_1 + 1} K S')) →
    (∀ (K : Submodule.{0, u_2} Complex Wp),
        LE.le.{u_2} K S →
          (∀ (B : Module.End.{0, u_2} Complex Wp),
              Membership.mem.{u_2, u_2} Gp B →
                ∀ (w : Wp),
                  Membership.mem.{u_2, u_2} K w →
                    Membership.mem.{u_2, u_2} K (DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1} B w)) →
            Or (Eq.{u_2 + 1} K Bot.bot.{u_2}) (Eq.{u_2 + 1} K S)) →
      (∀ (A : Module.End.{0, u_1} Complex Wq),
          Membership.mem.{u_1, u_1} Gq A →
            ∀ (v : Wq),
              Membership.mem.{u_1, u_1} S' v →
                Membership.mem.{u_1, u_1} S' (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} A v)) →
        ∀ (E Z : LinearMap.{0, 0, u_1, u_2} (RingHom.id.{0} Complex) Wq Wp),
          (∀ (v : Wq),
              Membership.mem.{u_1, u_1} S' v →
                Membership.mem.{u_2, u_2} S (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1} E v)) →
            (∀ (v : Wq),
                Membership.mem.{u_1, u_1} S' v →
                  Membership.mem.{u_2, u_2} S (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1} Z v)) →
              (∀ (A : Module.End.{0, u_1} Complex Wq),
                  Membership.mem.{u_1, u_1} Gq A →
                    Exists.{u_2 + 1} fun (B : Module.End.{0, u_2} Complex Wp) ↦
                      And
                        (Eq.{max (u_1 + 1) (u_2 + 1)} (LinearMap.comp.{0, 0, 0, u_1, u_1, u_2} E A)
                          (LinearMap.comp.{0, 0, 0, u_1, u_2, u_2} B E))
                        (Eq.{max (u_1 + 1) (u_2 + 1)} (LinearMap.comp.{0, 0, 0, u_1, u_1, u_2} Z A)
                          (LinearMap.comp.{0, 0, 0, u_1, u_2, u_2} B Z))) →
                (∀ (B : Module.End.{0, u_2} Complex Wp),
                    Membership.mem.{u_2, u_2} Gp B →
                      Exists.{u_1 + 1} fun (A : Module.End.{0, u_1} Complex Wq) ↦
                        And (Membership.mem.{u_1, u_1} Gq A)
                          (Eq.{max (u_1 + 1) (u_2 + 1)} (LinearMap.comp.{0, 0, 0, u_1, u_1, u_2} E A)
                            (LinearMap.comp.{0, 0, 0, u_1, u_2, u_2} B E))) →
                  (Exists.{u_1 + 1} fun (v : Wq) ↦
                      And (Membership.mem.{u_1, u_1} S' v)
                        (Ne.{u_2 + 1} (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1} E v) 0)) →
                    Exists.{1} fun (c : Complex) ↦
                      ∀ (v : Wq),
                        Membership.mem.{u_1, u_1} S' v →
                          Eq.{u_2 + 1} (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1} Z v)
                            (HSMul.hSMul.{0, u_2, u_2} c (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1} E v)) := by sorry
