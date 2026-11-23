-- Prove2me | Theorems.Thm_Bl_general_b_fact_rest_goal1
-- name    : Bl.general_b_fact_rest.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:25.317425+00:00
-- url     : https://prove2.me/theorems/34a991a9-a079-4ce9-ae2f-56e5c7b4a13d
-- title:
--   general b fact rest: goal1
-- statement:
--   The general b fact rest construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRest/Imports.lean#L7-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRest/Imports.lean#L7-L76

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRest_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact_rest

theorem Bl.general_b_fact_rest.goal1 :
  ∀ {R : Type u_1} [inst : CommRing.{u_1} R] [inst_1 : IsLocalRing.{u_1} R] [IsNoetherianRing.{u_1} R] {M : Type u_2}
  [inst_3 : AddCommGroup.{u_2} M] [inst_4 : Module.{u_1, u_2} R M] [Module.Finite.{u_1, u_2} R M] {p : Ideal.{u_1} R},
  Membership.mem.{u_1, u_1} (associatedPrimes.{u_1, u_2} R M) p →
    ∀ {x : R},
      Membership.mem.{u_1, u_1} (IsLocalRing.maximalIdeal.{u_1} R) x →
        IsSMulRegular.{u_1, u_2} M x →
          Exists.{u_1 + 1} fun (q : Ideal.{u_1} R) ↦
            And (Membership.mem.{u_1, u_1} (associatedPrimes.{u_1, u_2} R (QuotSMulTop.{u_2, u_1} x M)) q)
              (And (LT.lt.{u_1} p q) (And (Membership.mem.{u_1, u_1} q x) (Not (Membership.mem.{u_1, u_1} p x)))) := by sorry
