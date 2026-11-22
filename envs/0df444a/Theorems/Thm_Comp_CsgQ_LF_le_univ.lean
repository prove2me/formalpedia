-- Prove2me | Theorems.Thm_Comp_CsgQ_LF_le_univ
-- name    : Comp.CsgQ.LF_le_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:02:53.996546+00:00
-- url     : https://prove2.me/theorems/16f1d54d-497f-4210-9467-7ab9fe3c14ce
-- title:
--   Csg Q: LF le univ
-- statement:
--   The outer chain's first link, free: `Finset.univ` bounds everything.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L126-L129
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L126-L129

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.LF_le_univ (G : CsgQ S A1 A2) (h : G.WellFormed) (b : Finset S) :
    (G.toCSG h).LF ↑b ≤ (↑(Finset.univ : Finset S) : Set S) := by sorry
