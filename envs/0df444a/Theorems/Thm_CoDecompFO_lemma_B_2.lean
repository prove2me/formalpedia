-- Prove2me | Theorems.Thm_CoDecompFO_lemma_B_2
-- name    : CoDecompFO.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:48:46.229675+00:00
-- url     : https://prove2.me/theorems/79ca253a-0da4-4ef7-930d-cccdfe131e25
-- title:
--   Lemma B.2 (strengthened: at most $4b$ bags) — every tree co-decomposition has a binary form of the same width
-- statement:
--   Let $\mathcal T$ be a tree co-decomposition with $b$ bags. There is a co-decomposition $\mathcal T^*$ whose tree is binary, meaning rooted at some node $r^*$ with at most two children at every node, such that
--   $$
--   \lim\mathcal T\cong\lim\mathcal T^*,\qquad w(\mathcal T^*)=w(\mathcal T),\qquad \#\text{bags of }\mathcal T^*\le 4b .
--   $$
--   The isomorphism keeps coordinates: every bag $G_t$ of $\mathcal T$ occurs as a bag of $\mathcal T^*$ at a node $\iota(t)$, and the coordinate at $\iota(t)$ of the image of a family $x$ is $x_t$.
--
--   The bound on the number of bags keeps a linear-in-$b$ algorithm linear after the conversion.
--
--   Differences from the source:
--   - generalization: the number of bags of T* is O(b log b), and limT = limT* → at most 4b bags, and an isomorphism keeping the coordinates of the original bags; reason: the printed proof's O(log d(t)) bags per node cannot be, as a tree with d(t) labelled leaves has at least d(t) nodes; the construction gives Σ max(1, 2d(t) − 1) ≤ 4b, which implies the printed bound for b ≥ 2 and is what a time f·b needs
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Lemma B.2, pp.53–54; B.1, p.53

import Mathlib
import Definitions.Def_CoDecompFO_Lim

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **Lemma B.2** (Bumpus et al., arXiv:2611.04658, held file sha256 d550d7af…, pp.53–54), with the
number of bags at most `4b`: there is a tree co-decomposition `T*` that is binary (B.1, p.53: rooted at
some `r*`, with at most two children at every node), of the same width, with at most `4b` bags, and
with the same limit.

**Formalization Note** The paper prints `O(b log b)` bags, and its proof says the binary tree `T^t` has
`O(log d(t))` bags, which cannot be: a tree with `d(t)` labelled leaves has at least `d(t)` nodes. The
construction gives `Σ_t max(1, 2d(t) − 1) ≤ 4b` bags. "limT = limT*" is an isomorphism commuting with
the coordinates: every bag `G_t` reappears in `T*` at a node `ι t`, and the isomorphism keeps that
coordinate (compared through `Fin.val`, so no cast along `T*.bag (ι t) = T.bag t` is needed). -/
theorem lemma_B_2 {σ : Sig} (T : CoDecomp σ) :
    ∃ (Ts : CoDecomp σ) (rs : Fin Ts.b),
      (∀ t, {e | Ts.IsChildEdge rs t e}.ncard ≤ 2) ∧
      width Ts = width T ∧
      Ts.b ≤ 4 * T.b ∧
      ∃ (u : T.Lim ≃[σ.lang] Ts.Lim) (ι : Fin T.b → Fin Ts.b),
        ∀ t, Ts.bag (ι t) = T.bag t ∧ ∀ x, ((u x).val (ι t)).val = (x.val t).val := by sorry

end CoDecompFO
