-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_8
-- name    : AutobidSPPE.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:57:04.919463+00:00
-- url     : https://prove2.me/theorems/9c30f003-2786-406c-9c62-2acb83f5d502
-- title:
--   Lemma 2.8 — an ordered P-matrix criterion
-- statement:
--   Let $A=(a_{ij})\in\mathbb R^{m\times m}$ satisfy, for every row $i$,
--   $$
--   a_{ij}=-1\ (i<j),\qquad \sum_{j\ne i}(a_{ij})_+<1,\qquad a_{ii}>\sum_{j\ne i}(-a_{ij})_+ . \tag{25}
--   $$
--   Then $A$ is a **P-matrix**: every principal minor $\det A_{SS}$ with $S$ nonempty is positive. Here $(x)_+=\max\{x,0\}$.
--
--   The criterion is applied to the row-normalized spending Jacobian, whose entries above the diagonal equal $-1$ after sorting the endpoints.
--
--   **Formalization Note** Indices are `Fin m` in their natural order; the P-matrix notion is the published `PriceRobust.Stability.IsPMatrix`.
--
--   Differences from the source: none.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.8, (25), p.15

import Mathlib
import Definitions.Def_PriceRobust_Stability_ZPMatrix

namespace AutobidSPPE

/-- Lemma 2.8, p.15 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), an ordered P-matrix criterion: if `A ∈ ℝ^{m×m}` has
`aᵢⱼ = −1` for `i < j`, `∑_{j≠i} (aᵢⱼ)₊ < 1` and `aᵢᵢ > ∑_{j≠i} (−aᵢⱼ)₊` for every row `i`
(25), then `A` is a P-matrix (every nonempty principal minor is positive).

**Formalization Note** Indices are `Fin m` in their natural order; `(x)₊ = max x 0`. The P-matrix
notion is the published `PriceRobust.Stability.IsPMatrix`. -/
theorem lemma_2_8 {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hup : ∀ i j : Fin m, i < j → A i j = -1)
    (hpos : ∀ i : Fin m, ∑ j ∈ Finset.univ.erase i, max (A i j) 0 < 1)
    (hdiag : ∀ i : Fin m, ∑ j ∈ Finset.univ.erase i, max (-A i j) 0 < A i i) :
    PriceRobust.Stability.IsPMatrix A := by sorry

end AutobidSPPE
