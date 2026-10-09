-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_lemma_2_5
-- name    : CycleLengthsExp.ManyLengths.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:26.120343+00:00
-- url     : https://prove2.me/theorems/bd8412e3-97ae-4e31-b703-5275a94f767b
-- title:
--   Lemma 2.5 — a path of length ℓ from a prescribed vertex
-- statement:
--   Let $k$ and $\ell$ be positive integers, and let $G=(V,E)$ have more than $k$ vertices. Suppose every $k$-element vertex set $W$ has at least $\ell$ external neighbors. If the connected component containing $v$ has at least $k$ vertices, then there is a simple path starting at $v$ with exactly $\ell$ edges:
--   $$\exists P\text{ starting at }v,\qquad |E(P)|=\ell.$$
--
--   This is the path-existence statement used before constructing the long path outside the initial tree in the proof of Theorem 2.
--
--   **Formalization Note** The component size is the number of vertices reachable from $v$. The theorem formalizes the first assertion of Lemma 2.5; the subsequent “In particular” corollary is not a separate item here.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 6, Lemma 2.5, first assertion (cited as Lemma 2.4 on p. 13)

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- Friedman–Krivelevich, Lemma 2.5, p. 6, first assertion. -/
theorem lemma_2_5 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) (hV : k < Fintype.card V)
    (hW : ∀ W : Set V, W.ncard = k → ℓ ≤ (CycleLengthsExp.WellSpread.extNbhd G W).ncard)
    (v : V) (hv : k ≤ {w | G.Reachable v w}.ncard) :
    ∃ (w : V) (p : G.Walk v w), p.IsPath ∧ p.length = ℓ := by sorry

end CycleLengthsExp.ManyLengths
