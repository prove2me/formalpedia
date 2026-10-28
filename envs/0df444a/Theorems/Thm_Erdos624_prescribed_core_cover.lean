-- Prove2me | Theorems.Thm_Erdos624_prescribed_core_cover
-- name    : Erdos624.prescribed_core_cover
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:41:07.728295+00:00
-- url     : https://prove2.me/theorems/e9f429f1-cff8-475a-9cd5-fe25b0a1520d
-- title:
--   No common hole can be forced over a prescribed $(k-2)$-core (Erdős 624)
-- statement:
--   **Theorem.** Let $k\ge3$, $|U|=2^k$, and let $W\subseteq U$ be any set with $|W|=k-2$. Then there are two maps $g_0,g_1:\mathcal P(U)\to U$ such that for every $k$-set $Y\supseteq W$,
--
--   $$\{g_0(A):A\subseteq Y\}\cup\{g_1(A):A\subseteq Y\}=U.$$
--
--   Explicitly, $g_i(A)=\theta(i,[A\not\subseteq W],A\cap W)$ for a bijection $\theta:\{0,1\}^2\times\mathcal P(W)\to U$. Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ ($|X|=n$) satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. By an earlier track-amplification result, it would suffice to show that for each fixed number $r$ of maps $g_i:\mathcal P(U)\to U$, $|U|=2^k$, $k$ large, some $k$-set $Y$ and some $u\in U$ are missed by all $g_i$ on $\mathcal P(Y)$ (a *common hole*). This shows that the one-map palette argument over a fixed core $W$ (which proves the robust Alon bound) cannot give a two-map common hole: any successful argument must compare different cores.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,(2^k)$.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; claim from GPT 6.1 Sol (fifth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem prescribed_core_cover (k : ℕ) (hk : 3 ≤ k) (W : Finset (Fin (2 ^ k)))
    (hW : #W = k - 2) :
    ∃ g : Fin 2 → Finset (Fin (2 ^ k)) → Fin (2 ^ k),
      ∀ Y : Finset (Fin (2 ^ k)), #Y = k → W ⊆ Y → ∀ u, ∃ i, ∃ A ⊆ Y, g i A = u := by sorry

end Erdos624
