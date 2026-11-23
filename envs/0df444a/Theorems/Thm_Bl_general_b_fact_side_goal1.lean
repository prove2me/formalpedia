-- Prove2me | Theorems.Thm_Bl_general_b_fact_side_goal1
-- name    : Bl.general_b_fact_side.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:01.249656+00:00
-- url     : https://prove2.me/theorems/8dc53f7e-64bb-4d48-bdac-8ff233ccedf6
-- title:
--   general b fact side: goal1
-- statement:
--   The general b fact side construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSide/Imports.lean#L7-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSide/Imports.lean#L7-L36

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_3 u_4
open Bl Bl.general_b_fact_side

theorem Bl.general_b_fact_side.goal1 :
  ∀ {R : Type u_1} [inst : CommRing.{u_1} R] [inst_1 : IsLocalRing.{u_1} R] [IsNoetherianRing.{u_1} R] {N₁ : Type u_3}
  {N₂ : Type u_4} [inst_3 : AddCommGroup.{u_3} N₁] [inst_4 : Module.{u_1, u_3} R N₁] [Module.Finite.{u_1, u_3} R N₁]
  [inst_6 : AddCommGroup.{u_4} N₂] [inst_7 : Module.{u_1, u_4} R N₂] [Module.Finite.{u_1, u_4} R N₂],
  Not (Membership.mem.{u_1, u_1} (associatedPrimes.{u_1, u_3} R N₁) (IsLocalRing.maximalIdeal.{u_1} R)) →
    Not (Membership.mem.{u_1, u_1} (associatedPrimes.{u_1, u_4} R N₂) (IsLocalRing.maximalIdeal.{u_1} R)) →
      Exists.{u_1 + 1} fun (z : R) ↦
        And (Membership.mem.{u_1, u_1} (IsLocalRing.maximalIdeal.{u_1} R) z)
          (And (IsSMulRegular.{u_1, u_3} N₁ z) (IsSMulRegular.{u_1, u_4} N₂ z)) := by sorry
