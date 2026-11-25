-- Prove2me | Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_d1_apply
-- name    : Formalism.CoboundaryTransfers.WachMod.d1_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:20:37.891668+00:00
-- url     : https://prove2.me/theorems/93c508e1-7bd4-5aa8-966b-877c4146aca2
-- title:
--   Wach Mod: d1 apply
-- statement:
--   The Wach Mod construction uses the d1 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/MemCoboundariesOfIsOneCoboundary.lean#L70-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/MemCoboundariesOfIsOneCoboundary.lean#L70-L70

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
open Formalism.CoboundaryTransfers.WachMod
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)

theorem Formalism.CoboundaryTransfers.WachMod.d1_apply (y z : D) : W.d1 y z = (W.γ y - y) - (W.φ z - z) := by sorry
