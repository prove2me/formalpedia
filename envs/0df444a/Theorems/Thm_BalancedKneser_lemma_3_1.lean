-- Prove2me | Theorems.Thm_BalancedKneser_lemma_3_1
-- name    : BalancedKneser.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:45:34.749836+00:00
-- url     : https://prove2.me/theorems/9678e364-cab9-43f2-a0ae-811592e535ae
-- title:
--   Lemma 3.1 (Nonvanishing) — a proper $(d+2)$-coloring induces a nonzero map on $H_d(N(G);\mathbb F_2)$ (corrected: connectivity includes nonemptiness)
-- statement:
--   Let $G$ be a finite simple graph and $d\ge1$, and suppose that the neighborhood complex $N(G)$ is $(d-1)$-connected (nonempty, and every map $S^j\to|N(G)|$ with $0\le j\le d-1$ extends over the ball). Let $\kappa:V(G)\to[d+2]$ be a proper coloring. Since a face of $N(G)$ cannot use the color of its common neighbor, $\kappa$ induces a simplicial map $\kappa_N:N(G)\to\partial\Delta^{d+1}$, whose realization is
--   $$
--   x\ \longmapsto\ \Big(\sum_{v:\ \kappa(v)=i}x_v\Big)_{i\in[d+2]} .
--   $$
--   Then $H_d(\partial\Delta^{d+1};\mathbb F_2)\cong\mathbb F_2$, and the induced homomorphism
--   $$
--   (\kappa_N)_*:\ H_d(N(G);\mathbb F_2)\longrightarrow H_d(\partial\Delta^{d+1};\mathbb F_2)\cong\mathbb F_2
--   $$
--   is nonzero.
--
--   This is the topological constraint on colorings behind both chromatic lower bounds: Proposition 3.4 combines it with explicit generators of $H_d$.
--
--   **Formalization Note** Homology is singular homology of the realizations with coefficients in $\mathbb Z/2$. The statement asserts the existence of a continuous map $|N(G)|\to|\partial\Delta^{d+1}|$ given by the displayed formula with nonzero induced map; since the formula determines the map, nothing is lost.
--
--   Differences from the source:
--   - correction: t-connected: every map from S^j extends over a ball for 0 ≤ j ≤ t (p.6), which the empty space satisfies → IsConnectedUpTo also requires the space to be nonempty; reason: counterexample to the printed lemma: G the one-vertex graph, d = 1; N(G) has no face, so |N(G)| = ∅ is 0-connected in the printed sense, the constant coloring with colors in [3] is proper, and H₁(∅; F₂) = 0, so the induced map is zero
--   - reading: a graph G → a finite simple graph (Fintype V); reason: the proof (§9.1, p.17) uses that B(G) is a finite free Z₂-CW complex; every graph the paper applies the lemma to is finite
--   - encoding: simplicial homology of the complex → singular homology of its geometric realization (Hatcher.Singular.H); reason: the two agree for finite simplicial complexes; same groups
--   - encoding: the simplicial map κ_N : N(G) → ∂∆^{d+1} and (κ_N)_* → a continuous map of realizations with the affine formula x ↦ (Σ_{κ v = i} x_v)_i, and the map it induces on singular homology; reason: this formula is the geometric realization of κ_N
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Lemma 3.1, p.6 (PDF p.8); proof §9.1, pp.17–18 (PDF pp.19–20); t-connected, p.6

import Mathlib
import Definitions.Def_Hatcher_SingularHomology
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_BalancedKneser_nbhdComplex
import Definitions.Def_BalancedKneser_simplexBoundary
import Definitions.Def_BalancedKneser_IsConnectedUpTo

namespace BalancedKneser

/-- **Lemma 3.1 (Nonvanishing)** (Alipour–Jafari, arXiv:2611.04486v1, p.6 (PDF p.8); proof
§9.1, pp.17–18), with the corrected connectivity convention: "Let d ≥ 1, and suppose that N(G)
is (d − 1)-connected. Every proper coloring with colors in [d + 2] induces a nonzero
homomorphism (κ_N)_* : H_d(N(G); F2) → H_d(∂∆^{d+1}; F2) ≅ F2."

For a finite simple graph `G`, the coloring `κ` induces the simplicial map
`κ_N : N(G) → ∂∆^{d+1}` sending a vertex to its color; on realizations it is the affine map
`x ↦ (i ↦ Σ_{κ v = i} x_v)`. The statement asserts `H_d(|∂∆^{d+1}|; F₂) ≅ F₂` and that the
continuous map with this formula induces a nonzero map on `H_d(−; F₂)`.

Formalization Note: homology is singular homology of the realizations (`Hatcher.Singular`);
`IsConnectedUpTo` requires nonemptiness (the printed definition does not; without it the lemma
fails for the one-vertex graph, `d = 1`). Since the map is determined by its formula, the
existential loses nothing. -/
theorem lemma_3_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (d : ℕ)
    (hd : 1 ≤ d) (hconn : IsConnectedUpTo (TreeCoverLB.realization (nbhdComplex G)) (d - 1))
    (κ : G.Coloring (Fin (d + 2))) :
    Nonempty (Hatcher.Singular.H (ZMod 2) d (TreeCoverLB.realization (simplexBoundary (d + 2))) ≃ₗ[ZMod 2]
      ZMod 2) ∧
    ∃ f : C(TreeCoverLB.realization (nbhdComplex G), TreeCoverLB.realization (simplexBoundary (d + 2))),
      (∀ x, ((f x : TreeCoverLB.realization (simplexBoundary (d + 2))) : Fin (d + 2) → ℝ) =
        fun i => ∑ v ∈ Finset.univ.filter (fun v => κ v = i),
          (x : V → ℝ) v) ∧
      Hatcher.Singular.map (ZMod 2) d f ≠ 0 := by sorry

end BalancedKneser
