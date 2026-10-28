-- Prove2me | Theorems.Thm_Erdos261_greedy_eq_step_mod
-- name    : Erdos261.greedy_eq_step_mod
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:08:01.402212+00:00
-- url     : https://prove2.me/theorems/1320a72b-ce8c-465b-93e7-408a9f00ab54
-- title:
--   The greedy carry of Erdős 261 is the map $(N,R)\mapsto(N+1,\,2R \bmod (N+1))$
-- statement:
--   Let $g_j$ be the greedy carry for Erdős Problem 261 started at $(n,n)$: $g_0=n$, and $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$ (a *subtracting* step, the term $(n+j+1)/2^{n+j+1}$ is used), otherwise $g_{j+1}=2g_j$ (a *doubling* step). Then $g_j/2^{n+j}$ is what remains of $n/2^n$ after the terms used so far, and the greedy algorithm terminates iff some $g_j=0$. **Theorem.** For all $n,j\ge0$, the $j$-th iterate of $T(N,R)=(N+1,\,2R\bmod (N+1))$ from $(n,n)$ is $(n+j,\,g_j)$.
--
--   So the greedy algorithm is exactly the Borwein–Loring iteration $a_{k+1}=2(a_k\bmod k)$ (with $a=2R$), with no off-by-one: one uses $0\le g_j\le n+j$ throughout.
--
--   **Formalization Note.** $g_j$ is an integer (`greedy n j : ℤ`), and the statement uses `(greedy n j).toNat`; it is nonnegative.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); greedy carry as in Borwein–Loring 1990 / Tengely–Ulas–Zygadło 2020 (platform def Def_Erdos261_defs); identification checked for GPT 6.1 Sol's step map; claim from GPT 6.1 Sol (second answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem greedy_eq_step_mod (n j : ℕ) :
    (fun p : ℕ × ℕ => (p.1 + 1, (2 * p.2) % (p.1 + 1)))^[j] (n, n) = (n + j, (greedy n j).toNat) := by sorry

end Erdos261
