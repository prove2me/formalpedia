-- Prove2me | Theorems.Thm_Erdos180_flipBooleanColor_self
-- name    : Erdos180.flipBooleanColor_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T01:59:08.229685+00:00
-- url     : https://prove2.me/theorems/12ae5c69-9b2a-421f-90ee-f70febc296cc
-- title:
--   Flipping a colour at one vertex
-- statement:
--   Recolouring a single vertex $v$ changes its colour and nothing else:
--   $\mathrm{flip}(c,v)(v) = \lnot c(v)$.
--
--   The local move used to prove that a colouring maximising the cut can be assumed to place every
--   vertex on the side where it has more neighbours — the step that gives the bipartite subgraph of
--   Lemma 3.3 its edge bound.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L92-L96

import Definitions.Def_erdos180_core4
import Mathlib.Logic.Function.Basic

open Erdos180
open Finset SimpleGraph
open scoped Classical

@[simp]
theorem Erdos180.flipBooleanColor_self {V : Type*} [DecidableEq V]
    (color : V → Bool) (v : V) :
    flipBooleanColor color v v = ! color v := by sorry
