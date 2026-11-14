-- Prove2me | Theorems.Thm_ConsistentSubmodular_HardInstance_realization_bounds
-- name    : ConsistentSubmodular.HardInstance.realization_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:17.977181+00:00
-- url     : https://prove2.me/theorems/2a23c5db-1db3-4031-a2eb-e80efcafe206
-- title:
--   Value bounds for one realization on the hard stream
-- statement:
--   Consider the hard stream on $3k+2$ elements with weights $u_0,u_1,u_2\ge0$ for the three groups of cells and $u_2\le u_1$, and let $f_u$ be the weighted coverage. Let $(S_t)_{0\le t\le 3k+2}$ be a feasible trajectory with cardinality budget $k$ and change budget $C$ (with $k,C\in\mathbb N$), and let $c_g=c_g(S_{3k})$ be the number of tiny sets of group $g$ held at time $3k$. Then:
--
--   1. $f_u(S_{3k})\le u_0c_0+u_1c_1+u_2c_2$;
--   2. $f_u(S_{3k+1})\le u_0k+u_1C+u_1c_1+u_2c_2$;
--   3. $f_u(S_{3k+2})\le u_0k+u_1k+2u_2C+u_2c_2$;
--   4. $c_0+c_1+c_2\le k$.
--
--   At most $C$ sets are inserted at each update, and each new set outside $U_0$ has weight at most $u_1$ (using $u_2\le u_1$). This is the realization-wise bound of Appendix A.2 that is averaged over the randomness of the algorithm in the proof of Theorem 1.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardInstance.lean#L75-L139 (`ConsistentSubmodular.HardInstance.realization_bounds`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardInstance

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance

theorem ConsistentSubmodular.HardInstance.realization_bounds {k C : ℕ} {u : Fin 3 → ℝ} (hu : ∀ g, 0 ≤ u g)
    (hu21 : u 2 ≤ u 1) {S : Fin (3 * k + 2 + 1) → Finset (Fin (3 * k + 2))}
    (hS : FeasibleTrajectory k C S) :
    weightedValue k u (S (timeBefore k)) ≤
        u 0 * tinyCount k 0 (S (timeBefore k)) + u 1 * tinyCount k 1 (S (timeBefore k)) +
          u 2 * tinyCount k 2 (S (timeBefore k)) ∧
      weightedValue k u (S (timeMiddle k)) ≤
        u 0 * k + u 1 * C + u 1 * tinyCount k 1 (S (timeBefore k)) +
          u 2 * tinyCount k 2 (S (timeBefore k)) ∧
      weightedValue k u (S (timeAfter k)) ≤
        u 0 * k + u 1 * k + 2 * u 2 * C + u 2 * tinyCount k 2 (S (timeBefore k)) ∧
      (tinyCount k 0 (S (timeBefore k)) : ℝ) + tinyCount k 1 (S (timeBefore k)) +
        tinyCount k 2 (S (timeBefore k)) ≤ k := by sorry
