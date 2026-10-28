-- Prove2me | Theorems.Thm_Erdos261_greedy_phase_types_infinite
-- name    : Erdos261.greedy_phase_types_infinite
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:08:02.334734+00:00
-- url     : https://prove2.me/theorems/3a8d5aa8-457a-4538-94fd-3435abd3639b
-- title:
--   A non-terminating Erdős 261 greedy orbit has infinitely many doubling and infinitely many subtracting steps
-- statement:
--   Let $g_j$ be the greedy carry for Erdős Problem 261 started at $(n,n)$: $g_0=n$, and $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$ (a *subtracting* step, the term $(n+j+1)/2^{n+j+1}$ is used), otherwise $g_{j+1}=2g_j$ (a *doubling* step). Then $g_j/2^{n+j}$ is what remains of $n/2^n$ after the terms used so far, and the greedy algorithm terminates iff some $g_j=0$. **Theorem.** If $g_k\ne0$ for all $k$, then there are infinitely many $k$ with $2g_k<n+k+1$ (doubling) and infinitely many $k$ with $2g_k\ge n+k+1$ (subtracting).
--
--   If the steps were eventually all doubling, $g$ would grow like $2^t$ while the threshold grows linearly. If they were eventually all subtracting, the deficit $d_k=(n+k)-g_k$ would satisfy $d_{k+1}=2d_k+2$, so it grows exponentially, contradicting $0<g_k$, i.e. $d_k<n+k$.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); greedy carry as in Borwein–Loring 1990 / Tengely–Ulas–Zygadło 2020 (platform def Def_Erdos261_defs); Claim A1b of claim from GPT 6.1 Sol (second answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026) (the deficit recursion is $d\mapsto2d+2$, not $2d+1$ as stated there; the argument is unaffected)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem greedy_phase_types_infinite (n : ℕ) (hnt : ∀ k, greedy n k ≠ 0) :
    (∀ K, ∃ k ≥ K, 2 * greedy n k < ((n + k + 1 : ℕ) : ℤ)) ∧
    (∀ K, ∃ k ≥ K, ((n + k + 1 : ℕ) : ℤ) ≤ 2 * greedy n k) := by sorry

end Erdos261
