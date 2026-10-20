-- Prove2me | Theorems.Thm_AngelDevil_kingGuard_five_origin
-- name    : AngelDevil.kingGuard_five_origin
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-19T13:20:46.454399+00:00
-- url     : https://prove2.me/theorems/8799e326-d7d8-4969-9a45-0d8ed06b4322
-- title:
--   Five-burn preparation of a line guard
-- statement:
--   Starting with no blocked sites on a line, the Devil can prepare a blocked triple above a king in five burns, despite every intervening horizontal displacement being -1, 0, or 1.
--
--   The finite strategy predicate records four intervening moves and a final burn that completes the triple. This is the local preparation lemma used to guard a box boundary.
-- source:
--   Martin Kutz, The Angel Problem, Positional Games, and Digraph Roots (2004), Chapter 1, Section 1.1, pp. 2-3, Figures 1-3. https://people.mpi-inf.mpg.de/alumni/d1/2009/mkutz/diss/kutz_angel.pdf. Finite strategy certificate for Figure 2; index 4 represents five burns.

import Definitions.Def_AngelDevil_KingGuard

theorem AngelDevil.kingGuard_five_origin : AngelDevil.KingGuard 4 0 ∅ := by sorry
