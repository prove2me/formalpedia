-- Prove2me | Theorems.Thm_Comp_CsgQ_AF_eq_coe_of_fixed
-- name    : Comp.CsgQ.AF_eq_coe_of_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:01:41.88136+00:00
-- url     : https://prove2.me/theorems/ddabb82f-75e5-4fb4-a25a-131da6653fa7
-- title:
--   Csg Q: AF eq coe of fixed
-- statement:
--   **The almost-sure reachability set, exactly.** A region that is its own certified `μX` fixed
--       point and that the outer descent has reached *is* `AF b`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L128-L135
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L128-L135

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.AF_eq_coe_of_fixed (G : CsgQ S A1 A2) (h : G.WellFormed) (b y : Finset S)
    (hinner : ((G.toCSG h).AFInner ↑b ↑y).lfp = (↑y : Set S))
    (hy : (G.toCSG h).AF ↑b ≤ (↑y : Set S)) :
    (G.toCSG h).AF ↑b = (↑y : Set S) := by sorry
