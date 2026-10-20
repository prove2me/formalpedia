-- Prove2me | Theorems.Thm_AngelDevil_angelWins_mono
-- name    : AngelDevil.angelWins_mono
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-19T13:20:42.398014+00:00
-- url     : https://prove2.me/theorems/2c3d6ee4-b479-4ba2-87ca-270e8e9c8027
-- title:
--   Winning Angel strategies are monotone in power
-- statement:
--   For natural-number powers p ≤ q, if a single power-p Angel strategy survives against every Devil, then a power-q Angel has a winning strategy as well.
--
--   The game histories and Devil actions are unchanged when only the permitted jump radius increases.
-- source:
--   Andras Mathe, The Angel of power 2 wins (2007), Theorem 4.6 and Section 1 game definition; https://doi.org/10.1017/S0963548306008303. Elementary consequence of the Chebyshev jump rule, not a separately numbered theorem.

import Definitions.Def_AngelDevil_Game

theorem AngelDevil.angelWins_mono {p q : Nat} (hpq : p ≤ q) (h : AngelDevil.AngelWins p) : AngelDevil.AngelWins q := by sorry
