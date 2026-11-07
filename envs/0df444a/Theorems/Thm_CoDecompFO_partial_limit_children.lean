-- Prove2me | Theorems.Thm_CoDecompFO_partial_limit_children
-- name    : CoDecompFO.partial_limit_children
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:41.694208+00:00
-- url     : https://prove2.me/theorems/eb0664ac-7e0a-40a1-879d-59fabfed4a1e
-- title:
--   ¶2.13 with Lemmas 4.27–4.28 — partial limits are iterated pullbacks over the children
-- statement:
--   Let $\mathcal T$ be a tree co-decomposition with root $r$. For every node $t$, the partial limit $G[t]$ is isomorphic to the iterated pullback of $G_t$ with the partial limits $G[c]$ at the children $c$ of $t$: its points are tuples of a point $x_t\in G_t$ and points $\hat x_c\in G[c]$ with
--   $$
--   g^e_t(x_t)=g^e_c(\pi_c(\hat x_c))\quad\text{on each child edge } e=tc,
--   $$
--   and a relation holds iff it holds in $G_t$ and in each $G[c]$. The isomorphism is compatible with the projections. Moreover $G[r]\cong\lim\mathcal T$.
--
--   This is the recursion on which bottom-up processing rests.
--
--   Differences from the source:
--   - generalization: the displays G[t] = G[c] ×_{G_e} G_t (one child) and G[t] ≅ G₁[t] ×_{G_t} G₂[t] (two children, binary trees) → any number of children, including none; reason: ¶2.13 says the limit of a tree is an iterated pullback; zero, one and two children are the printed cases
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), ¶2.13, p.8; proof of Lemma 4.27, p.15; proof of Lemma 4.28, p.16

import Mathlib
import Definitions.Def_CoDecompFO_Lim

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **Partial limits are iterated pullbacks** (Bumpus et al., arXiv:2611.04658, held file sha256
d550d7af…, ¶2.13, p.8: "Since the indexing graph is a tree, the limit of T can also be computed
recursively by taking iterated pullbacks"; proof of Lemma 4.27, p.15: "G[t] = G[c] ×_{G_e} G_t"; proof
of Lemma 4.28, p.16: "G[t] ≅ G₁[t] ×_{G_t} G₂[t]").

For a root `r` and a node `t` with any number of children, `G[t]` is isomorphic to the structure of
tuples of a point of `G_t` and a point of `G[c]` at each child `c`, agreeing on the child edges,
compatibly with the projections; and `G[r]` is isomorphic to `lim T`.

**Formalization Note** The zero-child case is Lemma 4.26's leaf (p.15), and one and two children are the
printed displays. The general number of children specializes to them. -/
theorem partial_limit_children {σ : Sig} (T : CoDecomp σ) (r : Fin T.b) :
    (∀ t : Fin T.b, ∃ u : T.PartialLim r t ≃[σ.lang] T.ChildTuples r t,
      ∀ x : T.PartialLim r t,
        (u x).top = T.partialProj r t x ∧
        ∀ (e : {e // T.IsChildEdge r t e}) (s : Fin T.b)
          (hc : s ∈ T.subtree r (T.child e.1 t)) (ht : s ∈ T.subtree r t),
          ((u x).below e).val ⟨s, hc⟩ = x.val ⟨s, ht⟩) ∧
    (∃ v : T.PartialLim r r ≃[σ.lang] T.Lim,
      ∀ (x : T.PartialLim r r) (s : Fin T.b) (hs : s ∈ T.subtree r r),
        (v x).val s = x.val ⟨s, hs⟩) := by sorry

end CoDecompFO
