-- Prove2me | Theorems.Thm_DenseMatching_IPM_lemma_3_5
-- name    : DenseMatching.IPM.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:40:27.076618+00:00
-- url     : https://prove2.me/theorems/d0ae7e06-bcf2-4238-a596-7e4e8ab9c270
-- title:
--   Lemma 3.5 — Cheeger-type threshold cut for a nonnegative vector on a unit-weight multigraph
-- statement:
--   Let $G=(V_G,E_G,\mathbb 1)$ be a finite multigraph with unit weights, $D(G)$ its degree diagonal and $L(G)$ its Laplacian, and let $x\in\mathbb R^{V_G}_{\ge0}$ with $x^\top D(G)x>0$. There is a threshold $\theta>0$ such that $S_\theta=\{u:x_u>\theta\}$ has $\mathrm{Vol}_G(S_\theta)>0$ and
--   $$|E_G(S_\theta,V_G\setminus S_\theta)|\le\sqrt{\frac{2\,x^\top L(G)x}{x^\top D(G)x}}\;\mathrm{Vol}_G(S_\theta).$$
--   It is the cut step of the $\ell_2$ partition query of QueryDrivenPartition (Lemma 3.2).
--
--   Differences from the source:
--   - generalization: a multigraph with unit weights → UnitMultigraph: a finite edge type with two endpoint maps, parallel edges and loops allowed; deg_G(u) = number of edge ends at u (a loop counts twice); x⊤L(G)x = Σ_e (x_head − x_tail)², the quadratic form of L = D − A; reason: whether the page's multigraphs may carry loops is not said, so the statement covers both readings; the loopless multigraphs of §3 (clusters of a simple graph) are the special case, and a loop adds 0 to the cut and to x⊤L(G)x
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 20, Lemma 3.5

import Mathlib
import Definitions.Def_DenseMatching_IPM_Tools

namespace DenseMatching.IPM

/-- Lemma 3.5 (p. 20). Let `G` be a finite multigraph with unit weights (parallel edges and loops
allowed), `D(G)` its degree diagonal and `L(G)` its Laplacian, and let `x ∈ ℝ^V_{≥0}` with
`x⊤D(G)x > 0`. There is a threshold `θ > 0` such that `S_θ = {u : x_u > θ}` has `Vol_G(S_θ) > 0` and
`|E_G(S_θ, V \ S_θ)| ≤ √(2 x⊤L(G)x / x⊤D(G)x) · Vol_G(S_θ)`. -/
theorem lemma_3_5 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : UnitMultigraph V E) (x : V → ℝ) (hx : ∀ u, 0 ≤ x u)
    (hD : 0 < degreeQuad G x) :
    ∃ θ : ℝ, 0 < θ ∧ 0 < unitVolume G (Finset.univ.filter (fun u => θ < x u)) ∧
      (cutSize G (Finset.univ.filter (fun u => θ < x u)) : ℝ) ≤
        Real.sqrt (2 * lapQuad G x / degreeQuad G x) *
          (unitVolume G (Finset.univ.filter (fun u => θ < x u)) : ℝ) := by sorry

end DenseMatching.IPM
