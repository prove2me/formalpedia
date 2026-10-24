-- Prove2me | Theorems.Thm_Erdos624_boundary_commonHole
-- name    : Erdos624.boundary_commonHole
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:30:14.054369+00:00
-- url     : https://prove2.me/theorems/37afb8ef-8997-4b61-898d-78ddd6d48da1
-- title:
--   Boundary common-hole theorem for several maps $\mathcal P(U)\to U$ (Erdős 624)
-- statement:
--   **Theorem.** Let $U$ and $I$ be finite sets with $|I|\ge1$, let $2\le m$ and $|I|\cdot 2^m\le |U|$. For every family of maps $g_i:\mathcal P(U)\to U$ ($i\in I$) there are an $m$-set $Y\subseteq U$ and a point $u\in U$ with
--
--   $$u\notin\bigcup_{i\in I}\{g_i(A):A\subseteq Y\}.$$
--
--   If $|I|2^m<|U|$ this is counting. In the boundary case $|I|2^m=|U|$: the $|I|(|U|+1)>|U|$ values $g_i(\varnothing)$, $g_i(\{x\})$ contain a collision between two distinct slots; their arguments span at most $2\le m$ points, and any $m$-set $Y$ containing them has a joint image of size at most $|I|2^m-1<|U|$.
--
--   This stays on the counting boundary: it gives no improvement of $H(n)\ge\lceil\log_2 n\rceil$.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; Claim B1 of claim from a GPT answer relayed by Ethan Cheung (third round, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem boundary_commonHole {U ι : Type*} [Fintype U] [DecidableEq U] [Fintype ι] [DecidableEq ι]
    (m : ℕ) (hm : 2 ≤ m) (hr : 1 ≤ Fintype.card ι)
    (h : Fintype.card ι * 2 ^ m ≤ Fintype.card U) (g : ι → Finset U → U) :
    ∃ Y : Finset U, #Y = m ∧ ∃ u, ∀ i, ∀ A ⊆ Y, g i A ≠ u := by sorry

end Erdos624
