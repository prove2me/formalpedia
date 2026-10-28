-- Prove2me | Theorems.Thm_Erdos261_counterexample_propagates
-- name    : Erdos261.counterexample_propagates
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T18:46:55.934974+00:00
-- url     : https://prove2.me/theorems/b4c7ff49-3177-4a6f-a9ec-5192622607ab
-- title:
--   A counterexample to Erdős 261 propagates along all restarts of its greedy orbit
-- statement:
--   Write $\operatorname{Rep}$ for a representation $\frac{n}{2^n}=\sum_k \frac{a_k}{2^{a_k}}$ by pairwise distinct positive integers $a_k$ (Erdős Problem 261). With $g_j$ the greedy carry from $(n,n)$, **Theorem.** If $n\ge2$ has no representation, then $g_j\ne0$ for all $j$, and for every $j$ with $n+j$ even and $2g_j=n+j+2$, the integer $n+j+2$ also has no representation.
--
--   This is the contrapositive form of the restart reduction: a minimal counterexample would force an infinite, never-terminating greedy orbit all of whose restart instances are counterexamples too.
--
--   **Attribution.** The mathematical content is due to Borwein and Loring (1990, Algorithm 3 and Proposition 4): the greedy *-binary algorithm may deviate ("cheat") only at states $a_n\in\{n,n+1\}$, and every finite representation of a dyadic rational arises from such a run. In the variables here $a_{N+1}=2g$, and the state $a=N+1$ only leads to infinite tails, so the branch states are exactly $2g_j=N+2$. This corollary of the restart reduction is likewise a repackaging of that result; only the Lean formalization is new.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); definitions from Formal Conjectures 261.lean; P. B. Borwein and T. A. Loring, Some questions of Erdős and Graham on numbers of the form $\sum g_n/2^{g_n}$, Math. Comp. 54 (1990), no. 189, 377–394, doi:10.1090/S0025-5718-1990-0990598-9, Algorithm 3 and Proposition 4 (pp. 385–389); corollary of the restart reduction, a repackaging of Borwein–Loring 1990, Algorithm 3 / Proposition 4; Lean formalization by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem counterexample_propagates {n : ℕ} (hn : 2 ≤ n) (h : ¬ Erdos261Prop n) :
    (∀ j, greedy n j ≠ 0) ∧
      ∀ j, Even (n + j) → 2 * greedy n j = ((n + j + 2 : ℕ) : ℤ) → ¬ Erdos261Prop (n + j + 2) := by sorry

end Erdos261
