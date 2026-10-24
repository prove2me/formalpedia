-- Prove2me | Theorems.Thm_Erdos261_deficit_step
-- name    : Erdos261.deficit_step
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:27:29.471421+00:00
-- url     : https://prove2.me/theorems/ea17ac6a-e3e7-4b6a-a19b-02afcface3b6
-- title:
--   Erdős 261 greedy carry: a subtracting step sends the deficit $D$ to $2D+2$
-- statement:
--   Let $g_j$ be the greedy carry for Erdős Problem 261 started at $(n,n)$: $g_0=n$, and $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$ (a *subtracting* step), otherwise $g_{j+1}=2g_j$ (a *doubling* step). The greedy algorithm for $n/2^n=\sum a_k/2^{a_k}$ terminates iff some $g_j=0$. **Theorem.** Write $D_j=(n+j)-g_j$. If step $j$ is subtracting ($2g_j\ge n+j+1$), then
--
--   $$D_{j+1}=2D_j+2.$$
--
--   This corrects the recursion $D\mapsto 2D+1$ stated in an earlier version of the phase calculus; it is the elementary step behind the closed form for subtracting blocks (`subtracting_block`).
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); greedy carry as in Borwein–Loring 1990 / Tengely–Ulas–Zygadło 2020 (platform def Def_Erdos261_defs); (A.2) of claim from GPT 6.1 Sol (fourth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem deficit_step (n j : ℕ) (h : ((n + j + 1 : ℕ) : ℤ) ≤ 2 * greedy n j) :
    ((n + j + 1 : ℕ) : ℤ) - greedy n (j + 1) = 2 * (((n + j : ℕ) : ℤ) - greedy n j) + 2 := by sorry

end Erdos261
