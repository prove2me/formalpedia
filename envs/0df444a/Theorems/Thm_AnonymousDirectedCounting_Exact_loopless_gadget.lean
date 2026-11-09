-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_loopless_gadget
-- name    : AnonymousDirectedCounting.Exact.loopless_gadget
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:39.326518+00:00
-- url     : https://prove2.me/theorems/ff4695c4-82ab-4f4a-a744-76dee4b015d7
-- title:
--   Lemma 8 — loopless strongly connected gadget
-- statement:
--   Let $U,W$ be disjoint nonempty sets of agents with $|U|=\ell$, let $z\in U$, $z'\in W$ and $c\in\{1,\ell\}$. Writing $X\xrightarrow{d}Y$ for $d$ arcs from each agent of $X$ to each agent of $Y$, consider the graph on $U\cup W$ with exactly the arcs
--   $$
--   z\xrightarrow{c}W,\qquad z'\xrightarrow{1}U,\qquad U\setminus\{z\}\xrightarrow{\ell/c}z,\qquad W\setminus\{z'\}\xrightarrow{\ell}z.
--   $$
--   It is loopless and strongly connected. Each agent of $U\setminus\{z\}$ receives exactly one arc, from $z'$, and has outdegree $\ell/c$. Each agent of $W$ receives exactly $c$ arcs, all from $z$, and has outdegree $\ell$. This is the building block of the two phases of Theorem 4.
--
--   Differences from the source:
--   - encoding: sets of agents U, W and the graph on U ∪ W → U, W ⊆ Fin n with U ∪ W = univ; reason: any finite agent set is Fin n up to renaming
--   - encoding: receives only z′’s old vista; receives c copies of z’s old vista → the in-arc multiplicities from each sender; reason: the received multiset is determined by the in-arcs, and the graph has no state of its own
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Lemma 8, printed p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_NetworkModel

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

/-- Lemma 8, printed p. 21 (PDF p. 23). The graph on `U ∪ W` (here all of `Fin n`) with exactly the
four arc bundles is loopless and strongly connected; each agent of `U \ {z}` receives only one copy
of `z'`'s old vista and has outdegree `ℓ / c`; each agent of `W` receives only `c` copies of `z`'s
old vista and has outdegree `ℓ`. -/
theorem loopless_gadget {n : ℕ} (U W : Finset (Fin n)) (hdisj : Disjoint U W)
    (hcover : U ∪ W = Finset.univ) (ell c : ℕ) (hU : U.card = ell)
    (z z' : Fin n) (hz : z ∈ U) (hz' : z' ∈ W) (hc : c = 1 ∨ c = ell) :
    (∀ a : Fin n, gadgetArcs U W z z' c ell a a = 0) ∧
    StronglyConnected (gadgetArcs U W z z' c ell) ∧
    (∀ a ∈ U, a ≠ z →
      gadgetArcs U W z z' c ell z' a = 1 ∧
      (∀ y : Fin n, y ≠ z' → gadgetArcs U W z z' c ell y a = 0) ∧
      ∑ y : Fin n, gadgetArcs U W z z' c ell a y = ell / c) ∧
    (∀ a ∈ W,
      gadgetArcs U W z z' c ell z a = c ∧
      (∀ y : Fin n, y ≠ z → gadgetArcs U W z z' c ell y a = 0) ∧
      ∑ y : Fin n, gadgetArcs U W z z' c ell a y = ell) := by sorry

end AnonymousDirectedCounting.Exact
