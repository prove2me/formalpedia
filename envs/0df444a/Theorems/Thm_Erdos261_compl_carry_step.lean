-- Prove2me | Theorems.Thm_Erdos261_compl_carry_step
-- name    : Erdos261.compl_carry_step
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:30:11.047696+00:00
-- url     : https://prove2.me/theorems/b4b2aa52-5dfe-4fe3-a93c-1304d6ac1edf
-- title:
--   Complementary carry of the Erdős 261 greedy algorithm
-- statement:
--   Let $g_j$ be the greedy carry for Erdős Problem 261 started at $(n,n)$: $g_0=n$, and $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$ (a *subtracting* step), otherwise $g_{j+1}=2g_j$ (a *doubling* step). Equivalently $(N,R)\mapsto(N+1,\,2R\bmod(N+1))$ with $N_j=n+j$, $R_j=g_j$; the greedy algorithm terminates iff some $g_j=0$. **Theorem.** Put $D_j=(n+j+2)-g_j$. Then
--
--   $$D_{j+1}=\begin{cases}2D_j,&\text{step } j \text{ subtracting},\\ 2D_j-(n+j+1),&\text{step } j \text{ doubling}.\end{cases}$$
--
--   So on doubling runs $R=g$ doubles and on subtracting runs the complementary carry $D=N+2-R$ doubles.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); greedy carry as in Borwein–Loring 1990 / Tengely–Ulas–Zygadło 2020 (platform def Def_Erdos261_defs); Claim A1 of claim from a GPT answer relayed by Ethan Cheung (third round, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem compl_carry_step (n j : ℕ) :
    ((n + (j + 1) + 2 : ℕ) : ℤ) - greedy n (j + 1) =
      if ((n + j + 1 : ℕ) : ℤ) ≤ 2 * greedy n j
      then 2 * (((n + j + 2 : ℕ) : ℤ) - greedy n j)
      else 2 * (((n + j + 2 : ℕ) : ℤ) - greedy n j) - ((n + j + 1 : ℕ) : ℤ) := by sorry

end Erdos261
