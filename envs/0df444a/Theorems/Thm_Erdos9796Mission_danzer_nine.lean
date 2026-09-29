-- Prove2me | Theorems.Thm_Erdos9796Mission_danzer_nine
-- name    : Erdos9796Mission.danzer_nine
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-05T22:49:35.679361+00:00
-- url     : https://prove2.me/theorems/026148f7-dce3-4658-991b-75fa7cccf734
-- title:
--   Danzer's nine-point counterexample to the three-neighbour claim
-- statement:
--   There is a set $A$ of exactly nine distinct points in the Euclidean plane, each outside the convex hull of the other eight, such that for every $p\in A$ there is a positive radius $r_p$ with at least three points of $A$ at distance $r_p$ from $p$. The radius may depend on the vertex.
--
--   $$|A|=9,\qquad \forall p\in A\;\exists r_p>0:\;|\{q\in A:\|p-q\|=r_p\}|\ge3.$$
--
--   This known construction explains why the mission asks about four equidistant neighbours rather than three. It is a literature formalization milestone, not a claim that Problem 97 is settled.
-- source:
--   P. Erdős, Some Combinatorial and Metric Problems in Geometry (1987), pp. 175–176, Danzer's construction: https://www.renyi.hu/~p_erdos/1987-27.pdf

/- Statement-only mission draft: SKETCH — NOT PROMOTABLE.
Source and precise status are recorded in items.json. -/
import Definitions.Def_Erdos9796Mission
open Erdos9796Mission

theorem Erdos9796Mission.danzer_nine :
    ∃ A : Finset Plane, A.card = 9 ∧ ConvexIndep (A : Set Plane) ∧ HasNEquidistantProperty 3 A := by sorry
