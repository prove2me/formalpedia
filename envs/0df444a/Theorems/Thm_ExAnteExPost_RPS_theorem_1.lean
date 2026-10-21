-- Prove2me | Theorems.Thm_ExAnteExPost_RPS_theorem_1
-- name    : ExAnteExPost.RPS.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:38.878715+00:00
-- url     : https://prove2.me/theorems/c2ac9174-44b2-4596-89f3-55e683331eed
-- title:
--   Theorem 1, p. 9 — Birkhoff–von Neumann decomposition with floor/ceiling bounds on row and column sums
-- statement:
--   Let $X$ be a real $n \times m$ matrix (rows indexed by agents $N$, columns by goods $M$) such that
--
--   1. $X_{ij} \in [0,1]$ for every $i$ and $j$,
--   2. $\sum_{j} X_{ij} \le 1$ for every row $i$, and
--   3. $\sum_{i} X_{ij} \le 1$ for every column $j$.
--
--   Then there are integral ($0/1$) matrices $A^1, \dots, A^q$ and weights $w^1, \dots, w^q \in [0,1]$ such that
--   $$\sum_{k=1}^q w^k = 1, \qquad X = \sum_{k=1}^q w^k A^k,$$
--   and, for every $k$, every row $i$ and every column $j$,
--   $$\Big\lfloor \sum_{j'} X_{ij'} \Big\rfloor \le \sum_{j'} A^k_{ij'} \le \Big\lceil \sum_{j'} X_{ij'} \Big\rceil, \qquad \Big\lfloor \sum_{i'} X_{i'j} \Big\rfloor \le \sum_{i'} A^k_{i'j} \le \Big\lceil \sum_{i'} X_{i'j} \Big\rceil .$$
--
--   This is the general (rectangular, sub-stochastic) form of the Birkhoff–von Neumann theorem used by Recursive Probabilistic Serial to turn each fractional eating stage into a lottery over integral allocations. It also shows that an admissible decomposition rule exists, so the goal theorem is not vacuous. The square doubly stochastic case is the classical theorem (on Prove2Me: `FamousTheorems.birkhoff_von_neumann`).
--
--   **Formalization Note.** Integral matrices are represented as bundles $A^k_i = \{j : A^k_{ij} = 1\}$, so the column sum of $A^k$ is the number of agents holding good $j$. The paper's clause "in strongly polynomial time, one can compute" is dropped: only the existence of the decomposition is stated.
-- source:
--   Freeman, Shah, Vaish, Best of Both Worlds: Ex-Ante and Ex-Post Fairness in Resource Allocation, arXiv:2005.14122v1, p. 9, Theorem 1

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model

namespace ExAnteExPost.RPS
open Finset

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

/-- Theorem 1 (Birkhoff–von Neumann, general form), p. 9, existence part: a nonnegative matrix
with entries in `[0,1]` and row and column sums at most one is a convex combination of integral
allocations whose row and column sums are the floors or ceilings of those of `X`. -/
theorem theorem_1 (X : FracAlloc N G) (hX : BvNInput X) :
    ∃ d : Decomp N G, IsBvNDecomp X d := by sorry
end ExAnteExPost.RPS
