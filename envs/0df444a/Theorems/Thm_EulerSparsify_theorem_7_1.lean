-- Prove2me | Theorems.Thm_EulerSparsify_theorem_7_1
-- name    : EulerSparsify.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:28.224342+00:00
-- url     : https://prove2.me/theorems/4db520d1-9530-4792-8543-ee19cc58e178
-- title:
--   Theorem 7.1 — large level-set boundaries force small effective resistance
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph with nonnegative weights and let $W\subseteq V$ be such that the induced subgraph $G[W]$ is connected. Let $s,t\in W$ be distinct and let $\varphi$ be the potentials of a unit current from $s$ to $t$ in $G[W]$, that is $L_{G[W]}\varphi=\mathbf 1_s-\mathbf 1_t$. Let $\tfrac12<p<1$, $\beta>0$ and $c>0$, and suppose that every threshold $\theta$ with $\varphi(t)<\theta\le\varphi(s)$ satisfies
--
--   $$w\bigl(\partial_W S_\varphi[\theta]\bigr)\ \ge\ c\cdot\min\bigl\{\mathrm{vol}_\beta(S_\varphi[\theta]),\ \mathrm{vol}_\beta(W\setminus S_\varphi[\theta])\bigr\}^p ,\tag{7.1}$$
--
--   where $S_\varphi[\theta]=\{v\in W:\varphi(v)\ge\theta\}$ and $\mathrm{vol}_\beta$ is measured in $G$. Then
--
--   $$\mathrm{ER}_{G[W]}(s,t)\ \le\ \Bigl(\frac{8}{1-p}+\frac{16}{2p-1}\Bigr)\Bigl(\frac{1}{c\,\beta^{2p-1}}\Bigr)^{1/p}.$$
--
--   This is the analytic core of the electrical level-set decomposition: its contrapositive (Corollary 7.2) finds a cut with small boundary whenever the ER diameter is large, which drives Lemma 4.2.
--
--   Differences from the source:
--   - encoding: potential vector p ∈ ℝ^W → φ on V with L_{G[W]} φ = 1_s − 1_t; reason: p also names the exponent; values outside W are never read
--   - generalization: "Throughout this section we assume that G is connected" → only G[W] connected (through positive-weight edges); reason: the statement and proof use only G[W]; connected G is a special case
--   - generalization: graph → parallel edges and self-loops allowed; reason: parallel edges are part of an electrical network; a loop enlarges vol_β so (7.1) with loops implies (7.1) without; the conclusion is unchanged
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Theorem 7.1, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_restrict
import Definitions.Def_EulerSparsify_DiGraph_Reach
import Definitions.Def_EulerSparsify_DiGraph_effRes
import Definitions.Def_EulerSparsify_DiGraph_volReg
import Definitions.Def_EulerSparsify_DiGraph_boundary

namespace EulerSparsify

/-- **Theorem 7.1** (effective resistance from the boundaries of level sets), p.34, PDF p.36.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Theorem 7.1: "Let W ⊆ V be such that G[W] is connected, let s, t ∈ W be distinct, and let
p ∈ ℝ^W be the potentials of a unit current from s to t in G[W], that is L_{G[W]} p = 1_s − 1_t. Let
1/2 < p < 1, β > 0 and c > 0. Suppose that every θ with p(t) < θ ≤ p(s) satisfies
w(∂_W S_p[θ]) ≥ c · min{vol_β(S_p[θ]), vol_β(W ∖ S_p[θ])}^p. (7.1) Then
ER_{G[W]}(s, t) ≤ (8/(1 − p) + 16/(2p − 1)) · (1/(cβ^{2p−1}))^{1/p}."

**Formalization Note.**
* The paper uses `p` both for the potential vector and for the exponent; the potentials are `φ`
  here. `φ` is a vector on all of `V` with `L_{G[W]} φ = 1_s − 1_t`; its values outside `W` are
  free and never read (`L_{G[W]}` has zero rows there).
* `G[W] = G.restrict (G.inducedEdges W)`, connected on `W` through positive-weight edges.
  `S_φ[θ] = {v ∈ W : φ(v) ≥ θ}` (`levelSet`), `∂_W` = edges of `G[W]` with exactly one endpoint in
  the set (`DiGraph.boundary`), `vol_β` measured in `G` (§3, p.9; the proof uses
  `deg_G(v) ≥ deg_{G[W]}(v)`).
* Nonnegative weights; parallel edges and self-loops allowed (a loop enlarges `vol_β` and so only
  strengthens (7.1)). The section's "we assume G is connected" is not needed: only `G[W]` is. -/
theorem theorem_7_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (hw : ∀ e, 0 ≤ G.w e) (W : Finset V)
    (hW : (G.restrict (G.inducedEdges W)).ConnectedOn W) (s t : V) (hs : s ∈ W) (ht : t ∈ W)
    (hst : s ≠ t) (φ : V → ℝ)
    (hφ : (G.restrict (G.inducedEdges W)).lap.mulVec φ = Pi.single s 1 - Pi.single t 1)
    (p β c : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1) (hβ : 0 < β) (hc : 0 < c)
    (hlevel : ∀ θ : ℝ, φ t < θ → θ ≤ φ s →
      c * (min (G.volReg β (levelSet W φ θ)) (G.volReg β (W \ levelSet W φ θ))) ^ p ≤
        ∑ e ∈ G.boundary W (levelSet W φ θ), G.w e) :
    (G.restrict (G.inducedEdges W)).effRes s t ≤
      (8 / (1 - p) + 16 / (2 * p - 1)) * (1 / (c * β ^ (2 * p - 1))) ^ (1 / p) := by sorry

end EulerSparsify
