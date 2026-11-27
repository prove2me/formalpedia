-- Prove2me | Theorems.Thm_AlonMilman_PropertyT_Supplement_proposition_3_1
-- name    : AlonMilman.PropertyT.Supplement.proposition_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T03:28:50.46198+00:00
-- url     : https://prove2.me/theorems/546ab850-cb2e-4076-91d3-1d91aa392bb3
-- title:
--   Proposition 3.1 — diameter, maximal degree and $\lambda_1$ of a Cartesian product of connected graphs
-- statement:
--   Let $l \ge 1$ and, for $1 \le j \le l$, let $G_j$ be a finite connected graph with diameter $\rho_j$ and maximal degree $d_j$. Let $G = G_1 \times \dots \times G_l$ be their Cartesian product. Then
--
--   1. the diameter of $G$ is $\displaystyle\sum_{j=1}^{l} \rho_j$;
--   2. the maximal degree of $G$ is $\displaystyle\sum_{j=1}^{l} d_j$;
--   3. if every $G_j$ has at least two vertices, so that $\lambda_j = \lambda_1(G_j)$ (the second-smallest eigenvalue, with multiplicity, of $Q_{G_j} = \operatorname{diag}(d(v)) - A_{G_j}$) is defined, then
--   $$\lambda_1(G) = \min_{1 \le j \le l} \lambda_j.$$
--
--   Combined with the paper's spectral concentration estimate (Theorem 2.6), this computes all the parameters that the estimate needs for a product graph, and yields Theorem 3.2.
--
--   **Formalization Note** Graphs are finite `SimpleGraph`s; $\lambda_1$ is the published `AlonMilman.Diameter.lambda1`.
--
--   Differences from the source:
--   - encoding: the cartesian product of the l Gᵢ-s (iterated two-factor product) → one product on $\prod_j W_j$, adjacent iff the vertices differ in exactly one coordinate, along an edge of that factor; reason: the same graph up to the canonical identification of vertex sets.
--   - encoding: λᵢ = λ₁(Gᵢ) for every factor → the λ₁ clause is stated when every factor has at least two vertices, the diameter and degree clauses for all factors; reason: λ₁ of a one-vertex graph is undefined (the notation presupposes it), so this excludes only undefined cases.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), pp. 80–81, Proposition 3.1

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AlonMilman_PropertyT_Supplement_boxPi

namespace AlonMilman.PropertyT.Supplement

/-- Proposition 3.1 (Alon–Milman 1985, pp. 80–81). Let `G_1, …, G_l` (`l ≥ 1`) be finite
connected simple graphs with diameters `ρ_j`, maximal degrees `d_j` and `λ_j = λ₁(G_j)`, and let
`G` be their Cartesian product. Then `diam G = ∑ ρ_j`, the maximal degree of `G` is `∑ d_j`, and,
when every factor has at least two vertices (so that each `λ_j` is defined),
`λ₁(G) = min_j λ_j`. -/
theorem proposition_3_1 {l : ℕ} (hl : 0 < l) {W : Fin l → Type} [∀ j, Fintype (W j)]
    [∀ j, DecidableEq (W j)] (G : ∀ j, SimpleGraph (W j)) [∀ j, DecidableRel (G j).Adj]
    (hG : ∀ j, (G j).Connected) :
    (boxPi G).diam = ∑ j, (G j).diam ∧
    (boxPi G).maxDegree = ∑ j, (G j).maxDegree ∧
    ((∀ j, 2 ≤ Fintype.card (W j)) →
      AlonMilman.Diameter.lambda1 (boxPi G) =
        Finset.univ.inf' ⟨⟨0, hl⟩, Finset.mem_univ _⟩
          (fun j => AlonMilman.Diameter.lambda1 (G j))) := by sorry

end AlonMilman.PropertyT.Supplement
