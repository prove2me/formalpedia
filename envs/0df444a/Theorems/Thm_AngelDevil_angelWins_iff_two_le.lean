-- Prove2me | Theorems.Thm_AngelDevil_angelWins_iff_two_le
-- name    : AngelDevil.angelWins_iff_two_le
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-19T13:20:43.448913+00:00
-- url     : https://prove2.me/theorems/78319c36-be90-44b7-ae39-6f212616b326
-- title:
--   Complete classification by integer Angel power
-- statement:
--   In the standard infinite-board game against a Devil that burns at most one square per round, the Angel has a winning strategy exactly for natural-number powers p ≥ 2.
--
--   The negative cases are p=0 and p=1. The zero-power case is included because the formal parameter ranges over all natural numbers. This combines the known king-capture result with Mathe's power-two theorem and monotonicity.
-- source:
--   Martin Kutz, The Angel Problem, Positional Games, and Digraph Roots (2004), Chapter 1, Section 1.1, pp. 2-3, Figures 1-3. https://people.mpi-inf.mpg.de/alumni/d1/2009/mkutz/diss/kutz_angel.pdf. Andras Mathe, The Angel of power 2 wins (2007), Theorem 4.6 and Section 1 game definition; https://doi.org/10.1017/S0963548306008303. Logical combination of these published results.

import Definitions.Def_AngelDevil_Game

theorem AngelDevil.angelWins_iff_two_le (p : Nat) : AngelDevil.AngelWins p ↔ 2 ≤ p := by sorry
