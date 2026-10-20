-- Prove2me | Theorems.Thm_AngelDevil_king_box_step
-- name    : AngelDevil.king_box_step
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-19T13:20:45.910878+00:00
-- url     : https://prove2.me/theorems/933979c6-a215-44e2-b9ef-686e0ccba8dc
-- title:
--   Preservation of a guarded box against a chess king
-- statement:
--   Suppose the king is strictly inside the box [-100,100]^2, its corner boundary segments are blocked, and each side has a line guard whose preparation fits the remaining distance. Then there is a single square in the box for the Devil to block such that every subsequent legal king move preserves these conditions.
--
--   This formal invariant implements the four-side confinement argument; the constants are deliberately loose, not an optimal capture bound.
-- source:
--   Martin Kutz, The Angel Problem, Positional Games, and Digraph Roots (2004), Chapter 1, Section 1.1, pp. 2-3, Figures 1-3. https://people.mpi-inf.mpg.de/alumni/d1/2009/mkutz/diss/kutz_angel.pdf. Implementation of Figure 3 with radius 100 and seven-site corner arms, rather than the illustrated constants.

import Definitions.Def_AngelDevil_KingGuard

theorem AngelDevil.king_box_step (p : AngelDevil.Point) (B : Finset AngelDevil.Point) (h : AngelDevil.KingBoxReady p B) : ∃ z ∈ AngelDevil.kingBoard, ∀ q, AngelDevil.Jump 1 p q → q ∉ insert z B → AngelDevil.KingBoxReady q (insert z B) := by sorry
