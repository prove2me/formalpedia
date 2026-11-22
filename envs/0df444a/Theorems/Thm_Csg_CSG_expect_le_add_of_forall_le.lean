-- Prove2me | Theorems.Thm_Csg_CSG_expect_le_add_of_forall_le
-- name    : Csg.CSG.expect_le_add_of_forall_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:06:49.378689+00:00
-- url     : https://prove2.me/theorems/5357637a-88f3-4207-af59-9e0520f02d11
-- title:
--   CSG: expect le add of forall le
-- statement:
--   One-directional half of `expect_lipschitz`, in the `value_le_add_of_forall_le`/
--       `payoff_add_const` style already used in `MatrixGameMonotone.lean`: shifting every state's
--       continuation value up by at most `ε` shifts the expectation up by at most `ε`, since the
--       transition weights are nonnegative and sum to at most `1` (`expect_le_one`'s own `hmass`
--       argument, reused verbatim). Needs `0 ≤ ε` explicitly for the final `mul_le_mul_of_nonneg_right`
--       step: without it, `(Σ weights) * ε ≤ 1 * ε` could point the wrong way.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L138-L159
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L138-L159

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.expect_le_add_of_forall_le {s : S} {a1 : A1} {a2 : A2} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', v s' ≤ w s' + ε) : C.expect s a1 a2 v ≤ C.expect s a1 a2 w + ε := by sorry
