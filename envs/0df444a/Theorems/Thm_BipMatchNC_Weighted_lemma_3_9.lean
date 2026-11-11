-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_lemma_3_9
-- name    : BipMatchNC.Weighted.lemma_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:14:27.69602+00:00
-- url     : https://prove2.me/theorems/c47e0d01-2775-481e-82a1-c7076f761c76
-- title:
--   Lemma 3.9: D_w(t) = det(M(G, w)M(G, w)^T) is nonzero and |deg D_w(t) − 2rw*| ≤ 4n³δW
-- statement:
--   Let $G$ be a balanced bipartite graph on $[n]+[n]$ with weights $w:E\to\mathbb N$ that has a perfect matching, $w^*$ the maximum weight of a perfect matching and $W$ the maximum weight of an edge. Over $\mathbb Q$, let $\gamma$ have order at least $nr$, let $\alpha_1,\dots,\alpha_{n^2}$ be such that the $n^2r$ elements $\alpha_j\gamma^\ell$ are distinct, let $\delta\ge n$, $r>4n^3\delta W$, $D=n(r-\delta)$, and let $\mathcal D_w(t)=\det\big(M(G,w)M(G,w)^T\big)\in\mathbb Q[t]$. Then $\mathcal D_w(t)\neq0$ and
--   $$\big|\deg\mathcal D_w(t)-2rw^*\big|\le4n^3\delta W.$$
--
--   Since $r>4n^3\delta W$, this gives $|\deg\mathcal D_w/(2r)-w^*|<1/2$, so $w^*$ is the integer closest to $\deg\mathcal D_w(t)/(2r)$: the maximum weight is read off the degree of one determinant, which is how Theorem 3.5 computes it in $\mathrm{NC}^2$.
--
--   Differences from the source:
--   - reading: deg(D_w(t)) → D_w ≠ 0 is stated as a conclusion, and deg is natDegree; reason: the degree presupposes a nonzero polynomial; the proof shows it (the lower bound exhibits a nonzero top coefficient); stating it avoids the convention natDegree 0 = 0
--   - encoding: | deg(D_w(t)) − 2rw* | ≤ 4n³δW → the same inequality in ℤ; reason: exact integer arithmetic, no truncation
--   - encoding: §3.3 parameters: γ, α_1, …, α_{n²} as in §3.1, δ ≥ n, r > 4n³δW, D = n(r − δ), over the rationals (footnote 1, p. 18) → binders γ α : ℚ with OrderAtLeast γ (n * r) and injectivity of (j, ℓ) ↦ α j * γ ^ ℓ, n ≤ δ, 4 * n ^ 3 * δ * W < r, and D written as n * (r - δ) in ℕ; reason: standing assumptions of §3.1 and §3.3 (pp. 9, 13–14); if r ≤ δ (possible only when W = 0) the page's D = n(r − δ) is not a dimension, and the ℕ-subtraction makes D = 0, an empty-row matrix
--   - encoding: w* is the weight of a maximum weight perfect matching M* of G (p. 14), so G has one → hypothesis G.HasPM; w* is G.maxPMWeight w; reason: w* is only defined when a perfect matching exists
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 16 (PDF 17), Lemma 3.9 (with footnote 1, p. 18, PDF 19)

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Folded
import Definitions.Def_BipMatchNC_Weighted_Graph
import Definitions.Def_BipMatchNC_Weighted_MatchingMatrix

open Polynomial

namespace BipMatchNC.Weighted

theorem lemma_3_9 (n r δ : ℕ) (G : BipGraph n) (w : Fin n → Fin n → ℕ) (hPM : G.HasPM)
    (γ : ℚ) (α : Fin (n * n) → ℚ) (hγ : OrderAtLeast γ (n * r))
    (hα : Function.Injective fun x : Fin (n * n) × Fin r => α x.1 * γ ^ (x.2 : ℕ))
    (hδ : n ≤ δ) (hr : 4 * n ^ 3 * δ * G.maxEdgeWeight w < r) :
    detPoly γ α r (n * (r - δ)) G w ≠ 0 ∧
      |((detPoly γ α r (n * (r - δ)) G w).natDegree : ℤ) - 2 * r * (G.maxPMWeight w : ℤ)| ≤
        4 * (n : ℤ) ^ 3 * δ * (G.maxEdgeWeight w : ℤ) := by sorry

end BipMatchNC.Weighted
