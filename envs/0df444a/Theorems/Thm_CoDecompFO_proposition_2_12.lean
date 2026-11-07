-- Prove2me | Theorems.Thm_CoDecompFO_proposition_2_12
-- name    : CoDecompFO.proposition_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:48:43.191595+00:00
-- url     : https://prove2.me/theorems/4a640863-acc5-4ec0-9ab9-04256e742306
-- title:
--   Proposition 2.12 — the limit is universal among cones
-- statement:
--   Let $\mathcal T$ be a tree co-decomposition of $\sigma$-structures. A **cone** over $\mathcal T$ is a structure $H$ with homomorphisms $\varphi_a:H\to G_a$ for each node and each edge $a$ of the tree, such that $\varphi_e=g^e_t\circ\varphi_t$ for every node $t$ and incident edge $e$. For every cone there is a unique homomorphism
--   $$
--   u:H\to\lim\mathcal T
--   $$
--   commuting with the projections to the bags and the adhesions.
--
--   So the limit of ¶2.7 is the categorical limit of the diagram, which is what lets the limit be computed as an iterated pullback.
--
--   Differences from the source:
--   - generalization: the printed statement speaks of graphs and graph homomorphisms → any finite relational signature, with a structure H on any point set; reason: the graphs are the signature with one binary symbol, and footnote 1 (p.3) and A.5 extend the setting to structures
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Proposition 2.12, p.8; ¶2.11, p.7

import Mathlib
import Definitions.Def_CoDecompFO_Lim

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **Proposition 2.12** (Bumpus et al., arXiv:2611.04658, held file sha256 d550d7af…, p.8), for
`σ`-structures: "limT is universal among cones over T. That is, for every cone (H,{φ_a}) there exists
a unique graph homomorphism u: H → limT commuting with the projection maps."

A **cone** (¶2.11, p.7) is a structure `H` with homomorphisms `φ_a : H → G_a`, `a ∈ V(T) ∪ E(T)`,
with `φ_e = g^e_t ∘ φ_t` at each node `t` and incident edge `e`. -/
theorem proposition_2_12 {σ : Sig} (T : CoDecomp σ) (H : Type) [σ.lang.Structure H]
    (φt : (t : Fin T.b) → H → Fin (T.bag t).n) (φe : (e : Fin T.m) → H → Fin (T.adh e).n)
    (ht : ∀ t, IsHom σ (φt t)) (he : ∀ e, IsHom σ (φe e))
    (hl : ∀ e, φe e = T.gl e ∘ φt (T.ends e).1) (hr : ∀ e, φe e = T.gr e ∘ φt (T.ends e).2) :
    ∃! u : H →[σ.lang] T.Lim,
      (∀ t x, (u x).val t = φt t x) ∧ (∀ e x, CoDecomp.Lim.edgeProj e (u x) = φe e x) := by sorry

end CoDecompFO
