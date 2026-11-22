-- Prove2me | Theorems.Thm_Csg_CSG_expect_lipschitz
-- name    : Csg.CSG.expect_lipschitz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:53:56.437345+00:00
-- url     : https://prove2.me/theorems/e61f9bee-2ad9-4dd5-98f4-1a928580e730
-- title:
--   CSG: expect lipschitz
-- statement:
--   **Stage 2's key lemma.** `expect` moves by at most `ε` when the continuation does, in either
--       direction -- the one-step version of the Lipschitz bound this project already has for
--       `MatrixGame.value` (`MatrixGameMonotone.lean`'s `abs_value_sub_le`), needed to lift that bound
--       up through `stageGame`/`stageValue` in turn. Same `abs_le`-splitting shape as
--       `abs_value_sub_le` itself.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L166-L172
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L166-L172

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.expect_lipschitz {s : S} {a1 : A1} {a2 : A2} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) : |C.expect s a1 a2 v - C.expect s a1 a2 w| ≤ ε := by sorry
