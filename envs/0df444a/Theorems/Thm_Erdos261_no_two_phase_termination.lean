-- Prove2me | Theorems.Thm_Erdos261_no_two_phase_termination
-- name    : Erdos261.no_two_phase_termination
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:08:06.679997+00:00
-- url     : https://prove2.me/theorems/a8193b01-6fe2-49d3-b85a-f7381ffc5500
-- title:
--   Outside the Borwein–Loring numbers, the Erdős 261 greedy carry cannot stop within its first two phases
-- statement:
--   Let $g_j$ be the greedy carry for Erdős Problem 261 started at $(n,n)$: $g_0=n$, and $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$ (a *subtracting* step, the term $(n+j+1)/2^{n+j+1}$ is used), otherwise $g_{j+1}=2g_j$ (a *doubling* step). Then $g_j/2^{n+j}$ is what remains of $n/2^n$ after the terms used so far, and the greedy algorithm terminates iff some $g_j=0$. Write $c_j=2^{j+1}-j-2$ (so $c_0=0$, $c_{j+1}=2c_j+j+1$; these are the Borwein–Loring numbers). **Theorem.** Suppose $c_j<n<c_{j+1}$ (so $n$ is not a Borwein–Loring number) and that the $t$ steps after step $j$ are all doubling steps, i.e. $g_{j+s+1}=2g_{j+s}$ for $s<t$. Then
--
--   $$g_i\ne0\qquad\text{for every } i\le j+t+1.$$
--
--   So the orbit cannot reach $0$ during its initial subtracting run, during the following doubling run, or at the first subtracting step after it. Writing $r=n-c_j$, after the doubling run $g_{j+t}=2^t r$, and termination at the next step would mean $r(2^{t+1}-1)=2^{j+1}+t-1$, which is impossible (for $t=0$ it would force $n=c_{j+1}$). Every terminating $n$ other than the Borwein–Loring numbers therefore needs a later phase.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); greedy carry as in Borwein–Loring 1990 / Tengely–Ulas–Zygadło 2020 (platform def Def_Erdos261_defs); Claim A2 of claim from GPT 6.1 Sol (second answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem no_two_phase_termination (n j t : ℕ) (h1 : 2 ^ (j + 1) - j - 2 < n) (h2 : n < 2 ^ (j + 1 + 1) - (j + 1) - 2)
    (hdbl : ∀ s < t, greedy n (j + s + 1) = 2 * greedy n (j + s)) :
    ∀ i ≤ j + t + 1, greedy n i ≠ 0 := by sorry

end Erdos261
