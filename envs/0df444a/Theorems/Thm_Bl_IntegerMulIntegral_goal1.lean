-- Prove2me | Theorems.Thm_Bl_IntegerMulIntegral_goal1
-- name    : Bl.IntegerMulIntegral.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:20.355058+00:00
-- url     : https://prove2.me/theorems/50135bc8-742a-42d5-9a31-2d1d35bf4cbb
-- title:
--   Integer Mul Integral: goal1
-- statement:
--   The Integer Mul Integral construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/IntegerMulIntegral/IntMulIntegral.lean#L11-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/IntegerMulIntegral/IntMulIntegral.lean#L11-L39

import Mathlib
import Definitions.Def_Lemmata_IntegerMulIntegral_IntMulIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.IntegerMulIntegral

theorem Bl.IntegerMulIntegral.goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {n : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) (Fin n → E)) (v : Fin n → E),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (m : Int) ↦ And (Ne.{1} m 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} m v)) := by sorry
