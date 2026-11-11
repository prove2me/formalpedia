-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_claim_3_12
-- name    : BipMatchNC.Weighted.claim_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:15:32.107286+00:00
-- url     : https://prove2.me/theorems/803343ae-3005-43ad-8908-acc2d5216153
-- title:
--   Claim 3.12: when det(M(H)[S]) ≠ 0, the coefficient of t^{ŵ_S} in det(M(G, w)[S]) is det(M(H)[S]), and deg det(M(G, w)[S]) = ŵ_S
-- statement:
--   Work over $\mathbb Q$ with the parameters of §3.3 as in Observation 3.11: $G$ with a perfect matching, $\gamma$, $\alpha_1,\dots,\alpha_{n^2}$, $\delta\ge n$, $r>4n^3\delta W$, $D=n(r-\delta)$, a feasible dual $(y,z)$ of $G$ with tight subgraph $H$, and a set $S$ of $nD$ columns with $\det M(H)[S]\neq0$. Let $\hat w_S$ be the maximum $\hat w$-weight of a perfect matching of $G^{r,\delta}[S]$. Then, in $\mathbb Q[t]$,
--   $$[t^{\hat w_S}]\det M(G,w)[S]=\det M(H)[S]\ (\neq0),\qquad \deg\det M(G,w)[S]=\hat w_S,$$
--   where both column submatrices list the columns of $S$ in the same order.
--
--   This shows that the top coefficient of $\det M(G,w)[S]$ cannot cancel, which gives the lower bound $\deg\mathcal D_w(t)\ge2\hat w_S$ via the Cauchy–Binet expansion of $\mathcal D_w(t)$.
--
--   Differences from the source:
--   - generalization: (y, z) the optimal dual of Lemma 3.7 (y ≤ 0, z ≥ 0, value w*, |values| ≤ 2nW), H its tight subgraph and (ŷ, ẑ) its lift → any (y, z) with IsBalancedDualFeasible G.adj w y z; H = G.tightSubgraph w y z and (ŷ, ẑ) = (liftY D y, liftZ G r y z) built from it; reason: the dual of Lemma 3.7 is one such (y, z), so the statement specializes to the paper's
--   - encoding: S a subset of nD columns of M(H), M(H)[S] the square submatrix of the columns in S (in the natural order) → S : Finset (Fin (n * n) × Fin r) with a bijection e : Fin n × Fin D ≃ S, and colSubmatrix M S e; reason: |S| = nD is the existence of e; another column order multiplies each determinant by the same sign, so the hypothesis det ≠ 0 and the conclusions do not depend on it
--   - encoding: the coefficient of the term t^{ŵ_S}; deg → Polynomial.coeff and Polynomial.natDegree of det in ℚ[X] (t = X); reason: the coefficient is nonzero by hypothesis, so the determinant is a nonzero polynomial and natDegree is its degree
--   - encoding: ŵ_S = max{ ŵ(T) | T is a perfect matching in G^{r,δ}[S] } → blowUpPMWeight G w r D S, the maximum of Σ ŵ over bijections Fin n × Fin D ≃ S whose pairs are edges of G^{r,δ} (0 if there is none); reason: perfect matchings of a balanced graph are bijections; H^{r,δ}[S] ⊆ G^{r,δ}[S] has a perfect matching because det M(H)[S] ≠ 0, so the junk value 0 never occurs
--   - encoding: §3.3 parameters: γ, α_1, …, α_{n²} as in §3.1, δ ≥ n, r > 4n³δW, D = n(r − δ), over the rationals (footnote 1, p. 18) → binders γ α : ℚ with OrderAtLeast γ (n * r) and injectivity of (j, ℓ) ↦ α j * γ ^ ℓ, n ≤ δ, 4 * n ^ 3 * δ * W < r, and D written as n * (r - δ) in ℕ; reason: standing assumptions of §3.1 and §3.3 (pp. 9, 13–14); if r ≤ δ (possible only when W = 0) the page's D = n(r − δ) is not a dimension, and the ℕ-subtraction makes D = 0, an empty-row matrix
--   - encoding: w* is the weight of a maximum weight perfect matching M* of G (p. 14), so G has one → hypothesis G.HasPM; w* is G.maxPMWeight w; reason: w* is only defined when a perfect matching exists
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 17 (PDF 18), Claim 3.12 with the definition of ŵ_S

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Folded
import Definitions.Def_BipMatchNC_Weighted_Bipartite
import Definitions.Def_BipMatchNC_Weighted_Graph
import Definitions.Def_BipMatchNC_Weighted_MatchingMatrix
import Definitions.Def_BipMatchNC_Weighted_BlowUp

open Polynomial

namespace BipMatchNC.Weighted

theorem claim_3_12 (n r δ : ℕ) (G : BipGraph n) (w : Fin n → Fin n → ℕ) (hPM : G.HasPM)
    (γ : ℚ) (α : Fin (n * n) → ℚ) (hγ : OrderAtLeast γ (n * r))
    (hα : Function.Injective fun x : Fin (n * n) × Fin r => α x.1 * γ ^ (x.2 : ℕ))
    (hδ : n ≤ δ) (hr : 4 * n ^ 3 * δ * G.maxEdgeWeight w < r)
    (y z : Fin n → ℝ) (hfeas : IsBalancedDualFeasible G.adj w y z)
    (S : Finset (Fin (n * n) × Fin r)) (e : Fin n × Fin (n * (r - δ)) ≃ ↥S)
    (hdet : (colSubmatrix (matchingMatrix γ α r (n * (r - δ)) (G.tightSubgraph w y z)) S e).det
      ≠ 0) :
    (colSubmatrix (weightedMatchingMatrix γ α r (n * (r - δ)) G w) S e).det.coeff
        (blowUpPMWeight G w r (n * (r - δ)) S) =
      (colSubmatrix (matchingMatrix γ α r (n * (r - δ)) (G.tightSubgraph w y z)) S e).det ∧
    (colSubmatrix (weightedMatchingMatrix γ α r (n * (r - δ)) G w) S e).det.natDegree =
      blowUpPMWeight G w r (n * (r - δ)) S := by sorry

end BipMatchNC.Weighted
