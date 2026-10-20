-- Prove2me | Theorems.Thm_AngelDevil_power_one_devil_wins
-- name    : AngelDevil.power_one_devil_wins
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-19T13:20:43.072265+00:00
-- url     : https://prove2.me/theorems/26888492-cdea-4b37-b3a2-327d25204e18
-- title:
--   The Devil defeats the power-one Angel
-- statement:
--   There exists a single ordinary Devil strategy that defeats every power-one Angel strategy on the infinite board. Defeat means a finite round with an illegal jump or a landing on an already burned square.
--
--   The quantifier order is one Devil strategy against all Angel strategies, not a separate opponent chosen after each Angel strategy. The model allows the Angel to stay still and the Devil to burn the occupied square; only subsequent landings lose.
-- source:
--   Martin Kutz, The Angel Problem, Positional Games, and Digraph Roots (2004), Chapter 1, Section 1.1, pp. 2-3, Figures 1-3. https://people.mpi-inf.mpg.de/alumni/d1/2009/mkutz/diss/kutz_angel.pdf. Berlekamp chess-king capture argument. Formal implementation uses 56 preparatory burns in a radius-100 box, followed by finite exhaustion; no optimal deadline claimed.

import Definitions.Def_AngelDevil_Game

theorem AngelDevil.power_one_devil_wins : ∃ D : AngelDevil.DevilStrategy, ∀ A, ¬ AngelDevil.Survives 1 A D := by sorry
