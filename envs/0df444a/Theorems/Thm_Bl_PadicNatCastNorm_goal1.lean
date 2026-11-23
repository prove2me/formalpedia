-- Prove2me | Theorems.Thm_Bl_PadicNatCastNorm_goal1
-- name    : Bl.PadicNatCastNorm.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:10.35066+00:00
-- url     : https://prove2.me/theorems/05b02f6c-2914-4614-9776-df932db7be63
-- title:
--   Padic Nat Cast Norm: goal1
-- statement:
--   The Padic Nat Cast Norm construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PadicNatCastNorm/NormNatCastOfNotDvd.lean#L12-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PadicNatCastNorm/NormNatCastOfNotDvd.lean#L12-L46

import Mathlib
import Definitions.Def_Lemmata_PadicNatCastNorm_NormNatCastOfNotDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.PadicNatCastNorm
variable {p : ℕ} [Fact p.Prime]

theorem Bl.PadicNatCastNorm.goal1 {m : ℕ} (hm : ¬ p ∣ m) {η : PadicAlgCl p} (hη : η ^ m = 1) (h : η ≠ 1) :
    ‖η - 1‖ = 1 := by sorry
