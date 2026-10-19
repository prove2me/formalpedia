-- Prove2me | Theorems.Thm_AngelDevil_reducedJourney_is_journey
-- name    : AngelDevil.reducedJourney_is_journey
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-18T12:58:13.234791+00:00
-- url     : https://prove2.me/theorems/09953273-0806-4e9f-a1da-0b10a2292ffb
-- title:
--   Reduced journeys preserve the movement constraints
-- statement:
--   For any nonnegative integer power and any finite journey starting at the origin with each coordinate changing by at most that power per step, the earliest-predecessor reduction is again a journey with the same movement constraint. This states the structural validity of the reduction; the separate assertion about avoiding squares eaten by the transformed Devil is not included.
-- source:
--   Mathe, The Angel of power 2 wins (2007), https://doi.org/10.1017/S0963548306008303, author manuscript p. 3, equation (1) and the paragraph immediately following it.

import Definitions.Def_AngelDevil_ReducedJourney

theorem AngelDevil.reducedJourney_is_journey (p : Nat) (h : List AngelDevil.Point) (hj : AngelDevil.Journey p h) : AngelDevil.Journey p (AngelDevil.reducedJourney p h) := by sorry
