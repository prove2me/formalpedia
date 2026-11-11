-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_lemma_3
-- name    : CapacitatedKMedianFPT.Main.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:38.585606+00:00
-- url     : https://prove2.me/theorems/08ed4e73-1ba5-4399-9a11-a62ff385094c
-- title:
--   Lemma 3 — d(c, f) ≤ d̃(c, f) ≤ (d(c, f) + 2r̃_i)(1 + 2ε)
-- statement:
--   Let $I$ have positive integer distances at most $D=\lceil10n^2/\varepsilon\rceil$, $0<\varepsilon<1/2$, let $\ell_1,\dots,\ell_k$ be clients, $\tilde r_i\in\mathbb N$, $F_i$ the groups (3.6), $h(c)$ the index of a nearest leader of $c$, and $\tilde d$ the proxy distance. For every index $i\in[k]$, every client $c\in C$ and every facility $f\in F_i$,
--   $$d(c,f)\le\tilde d(c,f)\le\bigl(d(c,f)+2\tilde r_i\bigr)(1+2\varepsilon).$$
--
--   The proxy distance routes $c$ through the leader $\ell_i$; it is not itself a metric. The lower bound makes the weights $w=\tilde d-d$ nonnegative.
--
--   Differences from the source:
--
--   - generalization: the branch fixed by the enumeration: (ℓ, r̃) an entry of L, χ from an k-perfect family, h(c) = argmin with the source's ties → any leaders that are clients, any radii in ℕ, any coloring χ : P → [k], any permutation π and any nearest-leader choice h; reason: the statement uses only these properties; the source's branch is one instance
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 10, Lemma 3; p. 9–10, (3.6), h(c), α_(c,i), proxy distance

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance
import Definitions.Def_CapacitatedKMedianFPT_Main_Proxy

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

/-- **Lemma 3** (p. 10). For every `i ∈ [k]`, client `c` and facility `f ∈ F_i`,
`d(c, f) ≤ d̃(c, f) ≤ (d(c, f) + 2 r̃_i)(1 + 2ε)`. -/
theorem lemma_3 {P : Type} [Fintype P] [DecidableEq P] (I : Instance P) (ε : ℝ) (G : Guess I)
    (hI : I.IsValid) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hD : I.HasIntDistancesUpTo (distanceBound I.size ε))
    (hℓ : ∀ i, G.ℓ i ∈ I.C) (hh : G.IsNearestLeader) :
    ∀ (i : Fin I.k), ∀ c ∈ I.C, ∀ f ∈ G.group i,
      I.d c f ≤ G.proxyDist ε c f ∧
        G.proxyDist ε c f ≤ (I.d c f + 2 * (G.r i : ℝ)) * (1 + 2 * ε) := by sorry

end CapacitatedKMedianFPT.Main
