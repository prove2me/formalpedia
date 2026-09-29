-- Prove2me | Theorems.Thm_Erdos77_erdos_77_limit_exists
-- name    : Erdos77.erdos_77_limit_exists
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:34:54.181499+00:00
-- url     : https://prove2.me/theorems/fe6a0db7-055a-420a-9f2b-1d3b20d29fb7
-- title:
--   Erdős Problem 77: $\lim_{k\to\infty} R(k)^{1/k}$ exists
-- statement:
--   Let $R(k)$ denote the diagonal Ramsey number. Then the sequence $R(k)^{1/k}$ converges to a real limit: there is $L\in\mathbb R$ such that
--
--   $$
--   \lim_{k\to\infty} R(k)^{1/k}=L.
--   $$
--
--   Erdős asked for the value of this limit; it is not even known whether the limit exists. By the known bounds, if it exists then $\sqrt2\le L\le 3.8$.
--
--   **Formalization Note** The original problem asks for the *value* of the limit, which is unknown. This goal asserts only existence of the limit as a real number; determining the value is strictly stronger. $R(k)^{1/k}$ is the real power with exponent $1/k$ (the $k=0$ term does not affect the limit).
-- source:
--   Erdős Problems #77, https://www.erdosproblems.com/77 ; P. Erdős, Problems and results in combinatorial analysis and graph theory, Discrete Math. 72 (1988) 81–92; P. Erdős, Some of my favorite solved and unsolved problems in graph theory, Quaestiones Math. 16 (1993) 333–350.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

namespace Erdos77
theorem erdos_77_limit_exists :
    ∃ L : ℝ, Tendsto (fun k : ℕ ↦ (diagonalRamsey k : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 L) := by sorry
end Erdos77
