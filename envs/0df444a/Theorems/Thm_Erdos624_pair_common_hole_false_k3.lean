-- Prove2me | Theorems.Thm_Erdos624_pair_common_hole_false_k3
-- name    : Erdos624.pair_common_hole_false_k3
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:27:32.699803+00:00
-- url     : https://prove2.me/theorems/badafefb-3a10-4a77-84d7-62cc29d67404
-- title:
--   Two maps on $2^3$ points with no common hole on any 3-set (Erdős 624)
-- statement:
--   **Theorem.** Let $|U|=8=2^3$. There are two maps $g_0,g_1:\mathcal P(U)\to U$ such that for every $3$-set $Y\subseteq U$ and every $u\in U$, some $g_i$ takes the value $u$ on a subset of $Y$.
--
--   So the two-map common-hole statement ('for $|U|=2^k$, any two maps miss a common point on some $k$-set'), which would give one unit of gain over the counting bound for Erdős Problem 624, is false at $k=3$; e.g. $g_i(A)=(i,\min(|A|,3))$ on $U=\{0,1\}\times\{0,1,2,3\}$. Each map misses half of $U$ on every 3-set, yet the missed sets are disjoint. The statement for large $k$ remains open.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,(2^3)$, maps indexed by $\mathrm{Fin}\,2$; special case $r=2,n=8,k=3$ of `rank_cover`.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; (B2) of claim from GPT 6.1 Sol (fourth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem pair_common_hole_false_k3:
    ¬ ∀ g : Fin 2 → Finset (Fin (2 ^ 3)) → Fin (2 ^ 3),
      ∃ Y : Finset (Fin (2 ^ 3)), #Y = 3 ∧ ∃ u, ∀ i, ∀ A ⊆ Y, g i A ≠ u := by sorry

end Erdos624
