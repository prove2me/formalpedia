-- Prove2me | Theorems.Thm_Comp_CsgQ_LF_le_of_step
-- name    : Comp.CsgQ.LF_le_of_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:02:57.767805+00:00
-- url     : https://prove2.me/theorems/c64ad6ed-cfe0-48ca-8ae9-3c91d8132506
-- title:
--   Csg Q: LF le of step
-- statement:
--   One outer step is sound: if `c` is the certified `μX` fixed point at `y`, and `y` was an upper
--       bound on `LF b`, then `c` is too. The descent, one `OrderHom.gfp_le_of_step` per step, with the
--       middle chain's payoff supplying the step's identification.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L134-L141
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L134-L141

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.LF_le_of_step (G : CsgQ S A1 A2) (h : G.WellFormed) (b y c : Finset S)
    (hinner : ((G.toCSG h).LFInner ↑b ↑y).lfp = (↑c : Set S))
    (hy : (G.toCSG h).LF ↑b ≤ (↑y : Set S)) :
    (G.toCSG h).LF ↑b ≤ (↑c : Set S) := by sorry
