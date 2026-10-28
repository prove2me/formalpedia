-- Prove2me | Theorems.Thm_Erdos261_greedy_first_phase
-- name    : Erdos261.greedy_first_phase
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:07:59.750994+00:00
-- url     : https://prove2.me/theorems/cd87e6af-fafe-4d72-b5e5-0ac0e4ee89f8
-- title:
--   First phase of the Erdős 261 greedy carry in closed form
-- statement:
--   Let $g_j$ be the greedy carry for Erdős Problem 261 started at $(n,n)$: $g_0=n$, and $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$ (a *subtracting* step, the term $(n+j+1)/2^{n+j+1}$ is used), otherwise $g_{j+1}=2g_j$ (a *doubling* step). Then $g_j/2^{n+j}$ is what remains of $n/2^n$ after the terms used so far, and the greedy algorithm terminates iff some $g_j=0$. Write $c_j=2^{j+1}-j-2$ (so $c_0=0$, $c_{j+1}=2c_j+j+1$; these are the Borwein–Loring numbers). **Theorem.** If $c_j\le n$, then for every $i\le j$,
--
--   $$g_i=n-c_i,\qquad\text{and step } i \text{ is subtracting}\iff n\ge c_{i+1}.$$
--
--   Hence the greedy orbit starts with a run of exactly $j$ subtracting steps, where $c_j\le n<c_{j+1}$, and it terminates during this run iff $n=c_j$, i.e. exactly for the Borwein–Loring numbers $n=2^{j+1}-j-2$.
--
--   **Formalization Note.** $c_i$ is written with truncated subtraction `2 ^ (i + 1) - i - 2`, which is exact since $i+2\le 2^{i+1}$.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); greedy carry as in Borwein–Loring 1990 / Tengely–Ulas–Zygadło 2020 (platform def Def_Erdos261_defs); Claim A1c of claim from GPT 6.1 Sol (second answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem greedy_first_phase (n j : ℕ) (h : 2 ^ (j + 1) - j - 2 ≤ n) :
    ∀ i ≤ j, greedy n i = (n : ℤ) - ((2 ^ (i + 1) - i - 2 : ℕ) : ℤ) ∧
      (((n + i + 1 : ℕ) : ℤ) ≤ 2 * greedy n i ↔ 2 ^ (i + 1 + 1) - (i + 1) - 2 ≤ n) := by sorry

end Erdos261
