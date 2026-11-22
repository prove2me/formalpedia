-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_aF_empty
-- name    : Comp.CsgQ.coe_aF_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:07:38.66601+00:00
-- url     : https://prove2.me/theorems/6670ed69-d6cf-44de-af8c-a7f70da0d6dd
-- title:
--   Csg Q: coe a F empty
-- statement:
--   `aF` at the empty excused set, which is the only way `Apre1` ever calls `A` -- matching the
--       Java's own `A(mdist, new BitSet(), y)`. Stated separately so the `∅` on the `Set` side and the
--       `∅` on the `Finset` side are reconciled once.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L55-L57
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L55-L57

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.coe_aF_empty (G : CsgQ S A1 A2) (h : G.WellFormed) (y : Finset S) (s : S) :
    (↑(G.aF ∅ y s) : Set A1) = (G.toCSG h).A ∅ ↑y s := by sorry
