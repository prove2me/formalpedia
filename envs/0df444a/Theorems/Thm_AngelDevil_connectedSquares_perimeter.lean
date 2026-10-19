-- Prove2me | Theorems.Thm_AngelDevil_connectedSquares_perimeter
-- name    : AngelDevil.connectedSquares_perimeter
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:53:16.879236+00:00
-- url     : https://prove2.me/theorems/595569d4-9682-4a6c-9967-8e47f242c4c0
-- title:
--   Claim 4.2: boundary bound for connected squares
-- statement:
--   Let $S$ be a finite nonempty set of integer unit squares, connected by shared sides, and let $P(S)$ count all unit boundary sides, including boundaries of holes. Then
--
--   $$P(S) \le 2|S|+2.$$
--
--   This is the connected-square perimeter estimate used in the wall-counting argument for the Angel strategy.
-- source:
--   Mathe, The Angel of power 2 wins (2007), https://doi.org/10.1017/S0963548306008303, author manuscript p. 6, Definition 4.1 and Claim 4.2.

import Definitions.Def_AngelDevil_SquareBoundary

theorem AngelDevil.connectedSquares_perimeter {s : Finset AngelDevil.Point} (h : AngelDevil.SquaresConnected s) : AngelDevil.squarePerimeter s ≤ 2 * s.card + 2 := by sorry
