-- Prove2me | Theorems.Thm_Erdos77_erdos_lower_bound_1947
-- name    : Erdos77.erdos_lower_bound_1947
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T18:19:40.142244+00:00
-- url     : https://prove2.me/theorems/f8635a40-92cc-492e-ab77-47263dac9407
-- title:
--   Erdős 1947: $R(k) > 2^{k/2}$ for $k \ge 3$
-- statement:
--   For every integer $k\ge 3$, the diagonal Ramsey number satisfies
--
--   $$
--   R(k) > 2^{k/2}.
--   $$
--
--   This is Erdős's 1947 lower bound, one of the first applications of the probabilistic method. It shows $\liminf_{k\to\infty} R(k)^{1/k}\ge\sqrt2$, so any limit in Erdős Problem 77 is at least $\sqrt2$.
-- source:
--   P. Erdős, Some remarks on the theory of graphs, Bull. Amer. Math. Soc. 53 (1947), 292–294, https://doi.org/10.1090/S0002-9904-1947-08785-1 (main theorem: R(k) > 2^{k/2} for k ≥ 3).

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

namespace Erdos77
theorem erdos_lower_bound_1947 (k : ℕ) (hk : 3 ≤ k) :
    (2 : ℝ) ^ ((k : ℝ) / 2) < (diagonalRamsey k : ℝ) := by sorry
end Erdos77
