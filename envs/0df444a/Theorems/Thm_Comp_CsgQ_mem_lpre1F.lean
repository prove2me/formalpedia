-- Prove2me | Theorems.Thm_Comp_CsgQ_mem_lpre1F
-- name    : Comp.CsgQ.mem_lpre1F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:58:08.882218+00:00
-- url     : https://prove2.me/theorems/349d99fe-ff0d-4566-838d-ccb694868f4c
-- title:
--   Csg Q: mem lpre1 F
-- statement:
--   The Csg Q construction uses the mem lpre1 F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L77-L79
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L77-L79

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.mem_lpre1F (G : CsgQ S A1 A2) (w : S → Finset A1) (x : Finset S) (s : S) :
    s ∈ G.lpre1F w x ↔ G.bF (w s) x s = Finset.univ := by sorry
