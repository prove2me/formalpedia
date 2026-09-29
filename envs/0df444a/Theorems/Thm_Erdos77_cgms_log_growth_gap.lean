-- Prove2me | Theorems.Thm_Erdos77_cgms_log_growth_gap
-- name    : Erdos77_cgms_log_growth_gap
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T09:58:19.473979+00:00
-- url     : https://prove2.me/theorems/6c9c1d98-bf2d-4335-ae11-02c6c07af4f0
-- title:
--   CGMS logarithmic growth gap for the diagonal Ramsey number
-- statement:
--   There is a fixed real base a with 0 < a < 4 such that, for all sufficiently large natural numbers k, the natural logarithm of R(k) is at most k times the natural logarithm of a.
-- source:
--   Campos, Griffiths, Morris and Sahasrabudhe, An exponential improvement for diagonal Ramsey, arXiv:2303.09521, Theorems 11.1 and 1.1 and Section 12; https://arxiv.org/abs/2303.09521

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey

theorem Erdos77_cgms_log_growth_gap :
  Exists (fun a : Real =>
    And (0 < a) (And (a < 4) (Filter.Eventually (fun k : Nat =>
      Real.log (Erdos77.diagonalRamsey k) <= (k : Real) * Real.log a) Filter.atTop))) := by sorry
