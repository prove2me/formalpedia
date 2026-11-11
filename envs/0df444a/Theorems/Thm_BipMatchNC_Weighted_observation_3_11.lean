-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_observation_3_11
-- name    : BipMatchNC.Weighted.observation_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:15:40.669393+00:00
-- url     : https://prove2.me/theorems/939d901d-bff9-4c65-a2a6-2e2659c85943
-- title:
--   Observation 3.11: when det(M(H)[S]) ≠ 0, the lifted dual restricted to G^{r,δ}[S] is an optimal dual there and its value is the maximum weight of a perfect matching of G^{r,δ}[S]
-- statement:
--   Work over $\mathbb Q$ with the parameters of §3.3: $G$ a balanced bipartite graph on $[n]+[n]$ with weights $w$ and a perfect matching, $W$ its maximum edge weight, $\gamma$ of order at least $nr$, $\alpha_1,\dots,\alpha_{n^2}$ with the $n^2r$ elements $\alpha_j\gamma^\ell$ distinct, $\delta\ge n$, $r>4n^3\delta W$, $D=n(r-\delta)$. Let $(y,z)$ be a feasible dual solution of $G$, $H$ the subgraph of its tight edges, and $(\hat y,\hat z)$ the lifted dual on the blow-up graph $G^{r,\delta}$ (copies of $u_i$ get $y_{u_i}$, copies of $v_j$ get $z_{v_j}$, the vertices $a_{i,q}$ get $-y_{u_i}$). Let $S$ be a set of $nD$ right vertices (columns) with $\det M(H)[S]\neq0$. Then the restriction of $(\hat y,\hat z)$ to the vertices of $G^{r,\delta}[S]$ is a feasible and optimal dual solution of $G^{r,\delta}[S]$, and
--   $$\sum_{u}\hat y_u+\sum_{v\in S}\hat z_v=\hat w_S,$$
--   the maximum $\hat w$-weight of a perfect matching of $G^{r,\delta}[S]$.
--
--   This identifies $\hat w_S$ with an explicit sum of dual values, from which the lower bound (3.8) $\hat w_S\ge rw^*-2n^3\delta W$ and then the lower bound of Lemma 3.9 follow.
--
--   Differences from the source:
--   - generalization: (y, z) the optimal dual of Lemma 3.7 (y ≤ 0, z ≥ 0, value w*, |values| ≤ 2nW), H its tight subgraph and (ŷ, ẑ) its lift → any (y, z) with IsBalancedDualFeasible G.adj w y z; H = G.tightSubgraph w y z and (ŷ, ẑ) = (liftY D y, liftZ G r y z) built from it; reason: the dual of Lemma 3.7 is one such (y, z), so the statement specializes to the paper's
--   - generalization: an optimal dual solution for G^{r,δ}[S] → feasible and optimal among all duals of G^{r,δ}[S] with free y and z (IsBalancedDualFeasible); reason: G^{r,δ}[S] is balanced (|S| = nD), for which the page says z ≥ 0 can be skipped; optimality over the larger set implies it over the duals with z ≥ 0
--   - encoding: S a subset of nD columns of M(H), M(H)[S] the square submatrix of the columns in S (in the natural order) → S : Finset (Fin (n * n) × Fin r) with a bijection e : Fin n × Fin D ≃ S, and colSubmatrix M S e; reason: |S| = nD is the existence of e; another column order multiplies each determinant by the same sign, so the hypothesis det ≠ 0 and the conclusions do not depend on it
--   - encoding: the maximum weight of a perfect matching in G^{r,δ}[S] → blowUpPMWeight G w r D S (maximum over bijections Fin n × Fin D ≃ S whose pairs are edges); reason: perfect matchings of a balanced graph are bijections
--   - encoding: §3.3 parameters: γ, α_1, …, α_{n²} as in §3.1, δ ≥ n, r > 4n³δW, D = n(r − δ), over the rationals (footnote 1, p. 18) → binders γ α : ℚ with OrderAtLeast γ (n * r) and injectivity of (j, ℓ) ↦ α j * γ ^ ℓ, n ≤ δ, 4 * n ^ 3 * δ * W < r, and D written as n * (r - δ) in ℕ; reason: standing assumptions of §3.1 and §3.3 (pp. 9, 13–14); if r ≤ δ (possible only when W = 0) the page's D = n(r − δ) is not a dimension, and the ℕ-subtraction makes D = 0, an empty-row matrix
--   - encoding: w* is the weight of a maximum weight perfect matching M* of G (p. 14), so G has one → hypothesis G.HasPM; w* is G.maxPMWeight w; reason: w* is only defined when a perfect matching exists
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 17 (PDF 18), Observation 3.11 with the preceding setup

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Folded
import Definitions.Def_BipMatchNC_Weighted_Bipartite
import Definitions.Def_BipMatchNC_Weighted_Graph
import Definitions.Def_BipMatchNC_Weighted_MatchingMatrix
import Definitions.Def_BipMatchNC_Weighted_BlowUp

namespace BipMatchNC.Weighted

theorem observation_3_11 (n r δ : ℕ) (G : BipGraph n) (w : Fin n → Fin n → ℕ) (hPM : G.HasPM)
    (γ : ℚ) (α : Fin (n * n) → ℚ) (hγ : OrderAtLeast γ (n * r))
    (hα : Function.Injective fun x : Fin (n * n) × Fin r => α x.1 * γ ^ (x.2 : ℕ))
    (hδ : n ≤ δ) (hr : 4 * n ^ 3 * δ * G.maxEdgeWeight w < r)
    (y z : Fin n → ℝ) (hfeas : IsBalancedDualFeasible G.adj w y z)
    (S : Finset (Fin (n * n) × Fin r)) (e : Fin n × Fin (n * (r - δ)) ≃ ↥S)
    (hdet : (colSubmatrix (matchingMatrix γ α r (n * (r - δ)) (G.tightSubgraph w y z)) S e).det
      ≠ 0) :
    IsBalancedDualFeasible (blowUpAdjOn G r (n * (r - δ)) S) (blowUpWeightOn w r (n * (r - δ)) S)
        (liftY (n * (r - δ)) y) (fun b : ↥S => liftZ G r y z b.1) ∧
      (∀ (y' : Fin n × Fin (n * (r - δ)) → ℝ) (z' : ↥S → ℝ),
        IsBalancedDualFeasible (blowUpAdjOn G r (n * (r - δ)) S)
          (blowUpWeightOn w r (n * (r - δ)) S) y' z' →
        dualValue (liftY (n * (r - δ)) y) (fun b : ↥S => liftZ G r y z b.1) ≤ dualValue y' z') ∧
      dualValue (liftY (n * (r - δ)) y) (fun b : ↥S => liftZ G r y z b.1) =
        (blowUpPMWeight G w r (n * (r - δ)) S : ℝ) := by sorry

end BipMatchNC.Weighted
