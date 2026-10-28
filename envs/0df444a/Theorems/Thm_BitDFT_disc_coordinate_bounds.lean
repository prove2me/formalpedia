-- Prove2me | Theorems.Thm_BitDFT_disc_coordinate_bounds
-- name    : BitDFT.disc_coordinate_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:58:03.477625+00:00
-- url     : https://prove2.me/theorems/19a33043-7632-46a3-bb56-243caf4decd0
-- title:
--   A fixed-point unit-disc coordinate fits q bits or is exactly the boundary power of two
-- statement:
--   Let an integer pair z represent a complex value scaled by 2 to the power p, and suppose this value lies in the closed unit disc. Each integer coordinate has absolute value strictly below 2 to the power p, or exactly equal to it. The equality case matters when selecting the operand width for a multiplication algorithm with an arbitrary runtime bound.
-- source:
--   Coordinate range analysis for exact output scaling in the integer multiplication to DFT transfer.

import Definitions.Def_BitDFT_Numerics
open BitDFT

theorem BitDFT.disc_coordinate_bounds (p : ℕ) (z : ℤ × ℤ) (h : inDisc p z) :
    (z.1.natAbs < 2^p ∨ z.1.natAbs = 2^p) ∧
    (z.2.natAbs < 2^p ∨ z.2.natAbs = 2^p) := by sorry
