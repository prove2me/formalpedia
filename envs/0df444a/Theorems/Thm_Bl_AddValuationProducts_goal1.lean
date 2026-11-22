-- Prove2me | Theorems.Thm_Bl_AddValuationProducts_goal1
-- name    : Bl.AddValuationProducts.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:50.394188+00:00
-- url     : https://prove2.me/theorems/b2a4c330-eaa3-4471-b491-b37f055504b3
-- title:
--   Add Valuation Products: goal1
-- statement:
--   The Add Valuation Products construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/AddValuationProducts/AddValProd.lean#L17-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/AddValuationProducts/AddValProd.lean#L17-L57

import Mathlib
import Definitions.Def_Lemmata_AddValuationProducts_AddValProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.AddValuationProducts

theorem Bl.AddValuationProducts.goal1 :
  ∀ {O : Type u_1} [inst : CommRing.{u_1} O] [inst_1 : IsDomain.{u_1} O] [inst_2 : IsDiscreteValuationRing.{u_1} O]
  {ι : Type} [Fintype.{0} ι] [DecidableEq.{1} ι] (N : Submodule.{u_1, u_1} O (ι → O))
  (e :
    LinearEquiv.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} O) (ι → O)
      (Subtype.{u_1 + 1} fun (x : ι → O) ↦ Membership.mem.{u_1, u_1} N x)),
  Eq.{1} (Module.length.{u_1, u_1} O (HasQuotient.Quotient.{u_1, u_1} (ι → O) N))
    (DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O)
      (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} LinearMap.det.{u_1, u_1}
        (LinearMap.comp.{u_1, u_1, u_1, u_1, u_1, u_1} (Submodule.subtype.{u_1, u_1} N)
          (LinearEquiv.toLinearMap.{u_1, u_1, u_1, u_1} e)))) := by sorry
