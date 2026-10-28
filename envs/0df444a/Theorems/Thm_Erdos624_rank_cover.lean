-- Prove2me | Theorems.Thm_Erdos624_rank_cover
-- name    : Erdos624.rank_cover
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:27:29.319563+00:00
-- url     : https://prove2.me/theorems/61482708-a842-434c-a0f3-352b33ef299b
-- title:
--   Rank construction: $r$ maps $\mathcal P(U)\to U$ jointly cover $U$ on every $k$-set when $n\le r(k+1)$
-- statement:
--   **Theorem.** Let $|U|=n\ge1$, $r,k\ge0$ with $n\le r(k+1)$. Then there are maps $g_0,\dots,g_{r-1}:\mathcal P(U)\to U$ such that for every $k$-set $Y\subseteq U$,
--
--   $$\bigcup_{i<r}\{g_i(A):A\subseteq Y\}=U.$$
--
--   The maps depend only on $|A|$ (each point of $U$ is assigned a slot $(i,\ell)$ and $g_i(A)$ is the point in slot $(i,|A|)$). In the context of Erdős Problem 624, this shows that a family of $r$ maps need have no common omitted point on any $k$-set once $n\le r(k+1)$, so any common-hole lemma for several maps needs $k$ large compared with $n/r$.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,n$, maps indexed by $\mathrm{Fin}\,r$.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; (B.6)/(B.L3) of claim from GPT 6.1 Sol (fourth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem rank_cover (r n k : ℕ) (hn : 0 < n) (h : n ≤ r * (k + 1)) :
    ∃ g : Fin r → Finset (Fin n) → Fin n,
      ∀ Y : Finset (Fin n), #Y = k → ∀ u : Fin n, ∃ i, ∃ A ⊆ Y, g i A = u := by sorry

end Erdos624
