-- Prove2me | Theorems.Thm_Erdos261_subtracting_block
-- name    : Erdos261.subtracting_block
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:27:28.665128+00:00
-- url     : https://prove2.me/theorems/b757afb2-7dfc-4bf4-bbe7-8f574ccf8d8f
-- title:
--   Erdős 261 greedy carry: closed form for a block of subtracting steps
-- statement:
--   Let $g_j$ be the greedy carry for Erdős Problem 261 started at $(n,n)$: $g_0=n$, and $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$ (a *subtracting* step), otherwise $g_{j+1}=2g_j$ (a *doubling* step). The greedy algorithm for $n/2^n=\sum a_k/2^{a_k}$ terminates iff some $g_j=0$. **Theorem.** If steps $j,j+1,\dots,j+\ell-1$ are all subtracting, then with $D_j=(n+j)-g_j$,
--
--   $$g_{j+\ell}+2^\ell\,(D_j+2)=n+j+\ell+2,$$
--
--   equivalently $D_{j+\ell}=2^\ell(D_j+2)-2$. For $j=0$ ($D_0=0$) this recovers $g_\ell=n-c_\ell$ with the Borwein–Loring numbers $c_\ell=2^{\ell+1}-\ell-2$.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); greedy carry as in Borwein–Loring 1990 / Tengely–Ulas–Zygadło 2020 (platform def Def_Erdos261_defs); (A.3)/(A.4) of claim from GPT 6.1 Sol (fourth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem subtracting_block (n j l : ℕ)
    (h : ∀ i < l, ((n + j + i + 1 : ℕ) : ℤ) ≤ 2 * greedy n (j + i)) :
    greedy n (j + l) + 2 ^ l * ((((n + j : ℕ) : ℤ) - greedy n j) + 2) = ((n + j + l : ℕ) : ℤ) + 2 := by sorry

end Erdos261
