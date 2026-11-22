-- Prove2me | Theorems.Thm_Csg_CSG_Lpre1_empty_x
-- name    : Csg.CSG.Lpre1_empty_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:07:09.148404+00:00
-- url     : https://prove2.me/theorems/e718a642-7547-46b9-beff-a41bdc0dd69e
-- title:
--   CSG: Lpre1 empty x
-- statement:
--   **The payoff, a degeneracy at the escape target.** `Lpre1 ∅ y` is `∅` outright, for any `y`:
--       whatever `LW ∅ y s` converges to, `B`'s own escape test against the empty target `∅` always
--       fails (`CSG.B_empty_x`), regardless. Needed wherever a fixed-point iteration for an `LF`-style
--       operator starts its escape target from `⊥` (i.e. `∅`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeLimitSure.lean#L119-L127
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeLimitSure.lean#L119-L127

import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.Lpre1_empty_x (y : Set S) : C.Lpre1 (∅ : Set S) y = ∅ := by sorry
