-- Prove2me | Theorems.Thm_Bl_DiscreteValuationQuotients_goal1
-- name    : Bl.DiscreteValuationQuotients.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:13.633349+00:00
-- url     : https://prove2.me/theorems/c222304c-2c77-4197-96f3-666f3f6d0147
-- title:
--   Discrete Valuation Quotients: goal1
-- statement:
--   The Discrete Valuation Quotients construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/DiscreteValuationQuotients/LenQuotSpan.lean#L32-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/DiscreteValuationQuotients/LenQuotSpan.lean#L32-L77

import Mathlib
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.DiscreteValuationQuotients

theorem Bl.DiscreteValuationQuotients.goal1 :
  ∀ {O : Type u_1} {M : Type u_2} [inst : CommRing.{u_1} O] [inst_1 : IsDomain.{u_1} O]
  [inst_2 : IsDiscreteValuationRing.{u_1} O] [inst_3 : AddCommGroup.{u_2} M] [inst_4 : Module.{u_1, u_2} O M]
  [Module.Free.{u_1, u_2} O M] [Module.Finite.{u_1, u_2} O M]
  (φ : LinearMap.{u_1, u_1, u_2, u_2} (RingHom.id.{u_1} O) M M),
  Function.Injective.{u_2 + 1, u_2 + 1} (DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1} φ) →
    Eq.{1} (Module.length.{u_1, u_2} O (HasQuotient.Quotient.{u_2, u_2} M (LinearMap.range.{u_1, u_1, u_2, u_2} φ)))
      (DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O)
        (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_2 + 1, u_1 + 1} LinearMap.det.{u_2, u_1} φ)) := by sorry
