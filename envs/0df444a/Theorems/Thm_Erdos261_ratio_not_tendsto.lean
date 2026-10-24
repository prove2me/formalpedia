-- Prove2me | Theorems.Thm_Erdos261_ratio_not_tendsto
-- name    : Erdos261.ratio_not_tendsto
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:30:06.014245+00:00
-- url     : https://prove2.me/theorems/76898326-031f-48d4-b0bc-e35c364dd90c
-- title:
--   A non-terminating Erdős 261 greedy orbit has no limiting carry ratio
-- statement:
--   Let $g_j$ be the greedy carry for Erdős Problem 261 started at $(n,n)$: $g_0=n$, and $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$ (a *subtracting* step), otherwise $g_{j+1}=2g_j$ (a *doubling* step). Equivalently $(N,R)\mapsto(N+1,\,2R\bmod(N+1))$ with $N_j=n+j$, $R_j=g_j$; the greedy algorithm terminates iff some $g_j=0$. **Theorem.** If $g_k\ne0$ for all $k$, then $g_j/(n+j)$ does not converge.
--
--   With $x_j=g_j/(n+j)$ and $q_j\in\{0,1\}$ the decision at step $j$, $q_j=\frac{2g_j-g_{j+1}}{n+j+1}=2x_j\frac{n+j}{n+j+1}-x_{j+1}$. If $x_j\to L$ then $q_j\to L$, so $q_j$ is eventually constant, contradicting that both decisions occur infinitely often (`Erdos261.greedy_phase_types_infinite`).
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); greedy carry as in Borwein–Loring 1990 / Tengely–Ulas–Zygadło 2020 (platform def Def_Erdos261_defs); Claim A1 of claim from a GPT answer relayed by Ethan Cheung (third round, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026) (their displayed identity has $1+1/N_j$ where $N_j/(N_j+1)$ is correct; the limit argument is unaffected)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem ratio_not_tendsto (n : ℕ) (hnt : ∀ k, greedy n k ≠ 0) :
    ¬ ∃ L : ℝ, Filter.Tendsto (fun j : ℕ => (greedy n j : ℝ) / ((n : ℝ) + j)) Filter.atTop (nhds L) := by sorry

end Erdos261
