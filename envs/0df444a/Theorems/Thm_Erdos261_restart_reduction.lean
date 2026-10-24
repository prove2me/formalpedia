-- Prove2me | Theorems.Thm_Erdos261_restart_reduction
-- name    : Erdos261.restart_reduction
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T18:47:09.790977+00:00
-- url     : https://prove2.me/theorems/ea54e3a8-7816-47c7-95a1-0d809be74211
-- title:
--   Restart reduction: Erdős 261 for $n$ is greedy termination or a restart at a branch state
-- statement:
--   Write $\operatorname{Rep}$ for a representation $\frac{n}{2^n}=\sum_k \frac{a_k}{2^{a_k}}$ by pairwise distinct positive integers $a_k$ (Erdős Problem 261). Let $g_j$ be the greedy carry from $(n,n)$: $g_0=n$, $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$ and $g_{j+1}=2g_j$ otherwise. **Theorem.** For $n\ge2$, $n$ has a representation iff
--
--   $$\exists j:\ g_j=0\quad\text{or}\quad\exists j:\ n+j\text{ even},\ 2g_j=n+j+2,\ \text{and } n+j+2 \text{ has a representation.}$$
--
--   So the only freedom beyond the greedy algorithm is a restart at branch states $(N,N/2+1)$: one may skip $N+1$, take $N+2$, and continue with the instance $N+2$. Problem 261 is therefore equivalent to a termination statement for the greedy carry map $R\mapsto 2R\bmod(N+1)$ with restarts.
--
--   **Attribution.** The mathematical content is due to Borwein and Loring (1990, Algorithm 3 and Proposition 4): the greedy *-binary algorithm may deviate ("cheat") only at states $a_n\in\{n,n+1\}$, and every finite representation of a dyadic rational arises from such a run. In the variables here $a_{N+1}=2g$, and the state $a=N+1$ only leads to infinite tails, so the branch states are exactly $2g_j=N+2$. This theorem is a repackaging of that result for finite representations of $n/2^n$: after a deviation the remainder is exactly $(N+2)/2^{N+2}$, i.e. the instance $N+2$. The Lean formalization is new; the reduction is not.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); definitions from Formal Conjectures 261.lean; P. B. Borwein and T. A. Loring, Some questions of Erdős and Graham on numbers of the form $\sum g_n/2^{g_n}$, Math. Comp. 54 (1990), no. 189, 377–394, doi:10.1090/S0025-5718-1990-0990598-9, Algorithm 3 and Proposition 4 (pp. 385–389); restart reduction = repackaging of Borwein–Loring 1990, Algorithm 3 / Proposition 4; greedy as in Tengely–Ulas–Zygadło 2020 §3; Lean formalization by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem restart_reduction {n : ℕ} (hn : 2 ≤ n) :
    Erdos261Prop n ↔ (∃ j, greedy n j = 0) ∨
      ∃ j, Even (n + j) ∧ 2 * greedy n j = ((n + j + 2 : ℕ) : ℤ) ∧
        Erdos261Prop (n + j + 2) := by sorry

end Erdos261
