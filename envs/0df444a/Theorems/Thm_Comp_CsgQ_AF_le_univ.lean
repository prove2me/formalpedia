-- Prove2me | Theorems.Thm_Comp_CsgQ_AF_le_univ
-- name    : Comp.CsgQ.AF_le_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:58:33.656124+00:00
-- url     : https://prove2.me/theorems/47c81056-33e4-41cd-9336-e3090f59cd4e
-- title:
--   Csg Q: AF le univ
-- statement:
--   The outer descent's first link, free.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L111-L114
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L111-L114

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.AF_le_univ (G : CsgQ S A1 A2) (h : G.WellFormed) (b : Finset S) :
    (G.toCSG h).AF ↑b ≤ (↑(Finset.univ : Finset S) : Set S) := by sorry
