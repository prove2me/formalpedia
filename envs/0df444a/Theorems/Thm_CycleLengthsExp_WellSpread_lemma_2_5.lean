-- Prove2me | Theorems.Thm_CycleLengthsExp_WellSpread_lemma_2_5
-- name    : CycleLengthsExp.WellSpread.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:13.751809+00:00
-- url     : https://prove2.me/theorems/40e2bd45-2e26-4396-8d26-56df97b960bf
-- title:
--   Lemma 2.5, p. 6 — if every k-set has ≥ ℓ external neighbors, a path of length ℓ starts at any vertex of a component of size ≥ k
-- statement:
--   Let $k$ and $\ell$ be positive integers, and let $G=(V,E)$ be a graph on $n>k$ vertices in which every vertex set $W\subseteq V$ with $|W|=k$ satisfies $|N_G(W)|\ge\ell$. Let $v\in V$ be a vertex whose connected component has at least $k$ vertices. Then $G$ contains a path of length $\ell$ starting at $v$:
--
--   $$\exists\,w\in V\ \exists\text{ a path } v=x_0,x_1,\dots,x_\ell=w \text{ in } G.$$
--
--   This is the depth-first-search lemma; Theorem 1 uses it in the contracted graph of Lemma 2.4 to build the long path along which the cycles are routed.
--
--   **Formalization Note.** A path of length $\ell$ is a walk with $\ell$ edges and no repeated vertex. The "In particular" sentence of the lemma (a path of length $\lceil\alpha\lfloor k\rfloor\rceil$ in a $(k,\alpha)$-expander) is not posed separately.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 6, Lemma 2.5, first paragraph (proof cited from Proposition 2.1 of [19])

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

namespace CycleLengthsExp.WellSpread

theorem lemma_2_5 (n : ℕ) (G : SimpleGraph (Fin n)) (k ℓ : ℕ)
    (hk : 0 < k) (hℓ : 0 < ℓ) (hn : k < n)
    (hW : ∀ W : Set (Fin n), W.ncard = k → ℓ ≤ (extNbhd G W).ncard)
    (v : Fin n) (hv : k ≤ (G.connectedComponentMk v).supp.ncard) :
    ∃ (w : Fin n) (p : G.Walk v w), p.IsPath ∧ p.length = ℓ := by sorry

end CycleLengthsExp.WellSpread
