-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_fiber_separation
-- name    : AnonymousDirectedCounting.Exact.fiber_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:37.73513+00:00
-- url     : https://prove2.me/theorems/77a35c41-f384-4c88-a423-dd1791e96f14
-- title:
--   Lemma 6 — separation of nonleader fibers
-- statement:
--   Let $G$ be an admissible network with leader set $L$, $\ell=|L|$. Let $S\subsetneq V$ contain every leader, and let $h\ge0$. Suppose that for each $1\le r\le h$, every node of $\mathcal H_{r-1}$ whose fiber lies in $S$ has no arc from that fiber to $V\setminus S$ in round $r$. Then
--   $$
--   h\le|S|-\ell.
--   $$
--   This is what the sharp test uses to reject false candidates when $\ell\ge2$.
--
--   Differences from the source:
--   - encoding: anonymous agents and abstract history-tree nodes with fibers → external Fin n indexing, and nodes as values of History r with fibers computed from the network; reason: the index is absent from protocol inputs; two agents have equal History r exactly when they lie in one class of P_r, so nodes and vistas up to isomorphism are the same data
--   - encoding: h ≤ |S| − ℓ and the range 1 ≤ r ≤ h → h + ℓ ≤ |S| and r = i + 1 for i < h; reason: S contains every leader, so ℓ ≤ |S| and the two inequalities are the same; this avoids natural subtraction
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Lemma 6, printed p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_HistoryTree

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

/-- Lemma 6, printed p. 19 (PDF p. 21). `S ⊊ V` contains every leader; for each `1 ≤ r ≤ h`, written
`r = i + 1`, every node of `H_{r-1}` whose fiber lies in `S` sends no arc from that fiber out of `S`
in round `r`. Then `h ≤ |S| - ℓ`, written `h + ℓ ≤ |S|`. -/
theorem fiber_separation {n : ℕ} (G : NetworkModel n) (hG : Admissible G)
    (S : Finset (Fin n)) (hproper : S ≠ Finset.univ) (hleaders : G.leaders ⊆ S)
    (h : ℕ)
    (hclosed : ∀ i : ℕ, i < h → ∀ u ∈ historyLevel G i, fiberOf G i u ⊆ S →
      ∀ a ∈ fiberOf G i u, ∀ c : Fin n, c ∉ S → G.arcs (i + 1) a c = 0) :
    h + G.leaders.card ≤ S.card := by sorry

end AnonymousDirectedCounting.Exact
