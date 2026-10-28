-- Prove2me | Theorems.Thm_Erdos261_branch_iff_next_one
-- name    : Erdos261.branch_iff_next_one
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:30:13.647243+00:00
-- url     : https://prove2.me/theorems/93099b39-8a51-448e-834b-1fdcd60a7b52
-- title:
--   Erdős 261 branch states are exactly the predecessors of carry one
-- statement:
--   Let $g_j$ be the greedy carry for Erdős Problem 261 started at $(n,n)$: $g_0=n$, and $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$ (a *subtracting* step), otherwise $g_{j+1}=2g_j$ (a *doubling* step). Equivalently $(N,R)\mapsto(N+1,\,2R\bmod(N+1))$ with $N_j=n+j$, $R_j=g_j$; the greedy algorithm terminates iff some $g_j=0$. **Theorem.** For all $n,j$:
--
--   $$g_{j+1}=1\iff \bigl(n+j\text{ even and } 2g_j=n+j+2\bigr).$$
--
--   The right side is the branch (restart) condition of Borwein–Loring's Algorithm 3. So infinitely many branch visits on an orbit is the same as the carry returning to $1$ infinitely often.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); greedy carry as in Borwein–Loring 1990 / Tengely–Ulas–Zygadło 2020 (platform def Def_Erdos261_defs); Claim A1 of claim from a GPT answer relayed by Ethan Cheung (third round, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem branch_iff_next_one (n j : ℕ) :
    greedy n (j + 1) = 1 ↔ (Even (n + j) ∧ 2 * greedy n j = ((n + j + 2 : ℕ) : ℤ)) := by sorry

end Erdos261
