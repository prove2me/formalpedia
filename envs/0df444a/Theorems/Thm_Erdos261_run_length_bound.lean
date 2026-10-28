-- Prove2me | Theorems.Thm_Erdos261_run_length_bound
-- name    : Erdos261.run_length_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:30:08.529364+00:00
-- url     : https://prove2.me/theorems/88b23b4d-eb77-4b7b-bffb-8906316ced45
-- title:
--   Runs of the Erdős 261 greedy carry have logarithmic length
-- statement:
--   Let $g_j$ be the greedy carry for Erdős Problem 261 started at $(n,n)$: $g_0=n$, and $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$ (a *subtracting* step), otherwise $g_{j+1}=2g_j$ (a *doubling* step). Equivalently $(N,R)\mapsto(N+1,\,2R\bmod(N+1))$ with $N_j=n+j$, $R_j=g_j$; the greedy algorithm terminates iff some $g_j=0$. **Theorem.** Let $N=n+j\ge2$ and $h=\lceil\log_2 N\rceil$. Then the $h+2$ steps $j,\dots,j+h+1$ are not all subtracting, and, if $g_j\ge1$, they are not all doubling. Hence every maximal run of equal decisions starting at $N$ has length at most $\lceil\log_2 N\rceil+1$.
--
--   A doubling run gives $g_{j+L}=2^Lg_j\ge4N>N+L$, and a subtracting run gives $D_{j+L}=2^LD_j\ge8N>N+L+2$, contradicting $0\le g\le N$. (Close to Borwein–Loring 1990, Prop. 2 / Cor. 2 on strings of 0s and 1s.)
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); greedy carry as in Borwein–Loring 1990 / Tengely–Ulas–Zygadło 2020 (platform def Def_Erdos261_defs); Claim A1 of claim from a GPT answer relayed by Ethan Cheung (third round, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem run_length_bound (n j : ℕ) (hN : 2 ≤ n + j) :
    (1 ≤ greedy n j →
      ¬ ∀ i < Nat.clog 2 (n + j) + 2, 2 * greedy n (j + i) < ((n + (j + i) + 1 : ℕ) : ℤ)) ∧
    (¬ ∀ i < Nat.clog 2 (n + j) + 2, ((n + (j + i) + 1 : ℕ) : ℤ) ≤ 2 * greedy n (j + i)) := by sorry

end Erdos261
