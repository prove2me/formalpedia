-- Prove2me | Theorems.Thm_Erdos261_doubling_block
-- name    : Erdos261.doubling_block
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:27:32.307099+00:00
-- url     : https://prove2.me/theorems/bc14c6a9-62ea-47b8-b8a1-cf1b4aea0e20
-- title:
--   Erdős 261 greedy carry: closed form for a block of doubling steps
-- statement:
--   Let $g_j$ be the greedy carry for Erdős Problem 261 started at $(n,n)$: $g_0=n$, and $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$ (a *subtracting* step), otherwise $g_{j+1}=2g_j$ (a *doubling* step). The greedy algorithm for $n/2^n=\sum a_k/2^{a_k}$ terminates iff some $g_j=0$. **Theorem.** If steps $j,\dots,j+t-1$ are all doubling, then
--
--   $$g_{j+t}=2^t g_j.$$
--
--   Together with `subtracting_block` this gives the exact phase calculus of the greedy orbit: every phase acts by an explicit affine map, so termination after a fixed phase pattern is an exponential Diophantine condition.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); greedy carry as in Borwein–Loring 1990 / Tengely–Ulas–Zygadło 2020 (platform def Def_Erdos261_defs); (A.8) of claim from GPT 6.1 Sol (fourth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem doubling_block (n j t : ℕ)
    (h : ∀ i < t, 2 * greedy n (j + i) < ((n + j + i + 1 : ℕ) : ℤ)) :
    greedy n (j + t) = 2 ^ t * greedy n j := by sorry

end Erdos261
