-- Prove2me | Theorems.Thm_Bl_general_b_fact_tail_goal1
-- name    : Bl.general_b_fact_tail.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:10.65+00:00
-- url     : https://prove2.me/theorems/b1e4bd27-2de7-4025-aaf2-49eed40b9fc8
-- title:
--   general b fact tail: goal1
-- statement:
--   The general b fact tail construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactTail/Imports.lean#L7-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactTail/Imports.lean#L7-L37

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactTail_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open Bl Bl.general_b_fact_tail

theorem Bl.general_b_fact_tail.goal1 :
  ∀ {R : Type u_1} {M : Type u_2} [inst : CommRing.{u_1} R] [inst_1 : IsDomain.{u_1} R]
  [inst_2 : IsPrincipalIdealRing.{u_1} R] [inst_3 : AddCommGroup.{u_2} M] [inst_4 : Module.{u_1, u_2} R M]
  {ι : Type u_3} [inst_5 : Fintype.{u_3} ι] [DecidableEq.{u_3 + 1} ι] (b : Module.Basis.{u_3, u_1, u_2} ι R M)
  (N : Submodule.{u_1, u_2} R M)
  (h :
    Eq.{1} (Module.finrank.{u_1, u_2} R (Subtype.{u_2 + 1} fun (x : M) ↦ Membership.mem.{u_2, u_2} N x))
      (Module.finrank.{u_1, u_2} R M))
  (e :
    LinearEquiv.{u_1, u_1, u_2, u_2} (RingHom.id.{u_1} R) M
      (Subtype.{u_2 + 1} fun (x : M) ↦ Membership.mem.{u_2, u_2} N x)),
  Associated.{u_1}
    (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_2 + 1, u_1 + 1} LinearMap.det.{u_2, u_1}
      (LinearMap.comp.{u_1, u_1, u_1, u_2, u_2, u_2} (Submodule.subtype.{u_1, u_2} N)
        (LinearEquiv.toLinearMap.{u_1, u_1, u_2, u_2} e)))
    (Finset.prod.{u_3, u_1} Finset.univ.{u_3} fun (i : ι) ↦ Submodule.smithNormalFormCoeffs.{u_3, u_1, u_2} b h i) := by sorry
