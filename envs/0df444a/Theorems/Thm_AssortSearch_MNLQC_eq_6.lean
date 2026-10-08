-- Prove2me | Theorems.Thm_AssortSearch_MNLQC_eq_6
-- name    : AssortSearch.MNLQC.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:34.31988+00:00
-- url     : https://prove2.me/theorems/cd3361c0-671e-48db-8e6e-810fa9ff6bfd
-- title:
--   (6): the derivative $h^{m\prime}(v_j)$ = numerator$/(v_j + V_S)^2$
-- statement:
--   Let $v_1,\dots,v_n > 0$ be the variants' preferences, $v_0 > 0$ the no-purchase preference, $m_1,\dots,m_n$ real margins, and $c$ an operational cost function that is concave and increasing on $[0,1]$. Assume also that $c$ is differentiable on $(0,1)$. Fix an assortment $S$ and a variant $j \notin S$, and write $V_S = v_0 + \sum_{i \in S} v_i$. Let $h^m(v_j) = \pi_j^m(v_j) - L^m(v_j)$ be the profit change from adding $j$ with preference $v_j$ under the MNL model without search.
--
--   Then, for every $v_j > 0$, $h^m$ is differentiable at $v_j$ and
--
--   $$h^{m\prime}(v_j) = \frac{\Big[m_j V_S - c'\Big(\frac{v_j}{v_j+V_S}\Big) V_S\Big] - \Big[\sum_{i\in S} m_i v_i - \sum_{i\in S} c'\Big(\frac{v_i}{v_j+V_S}\Big) v_i\Big]}{(v_j+V_S)^2}.$$
--
--   This is display (6) in the proof of Theorem 4. The sign of $h^{m\prime}$ is therefore the sign of the numerator, which is what the rest of the proof studies.
--
--   **Formalization Note** The paper writes a common margin $m$ in both brackets. The statement keeps the model's per-variant margins, $m_j$ in the first bracket and $m_i$ in the sum, and reduces to the printed formula when all margins are equal. Differentiability of $c$ on $(0,1)$ is added here because the paper differentiates $c$ in (6). The goal theorem does not assume it. The derivative is claimed only for $v_j > 0$, because at $v_j = 0$ the demand $v_j/(v_j + V_S)$ is $0$, an endpoint of $c$'s domain.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 14 (PDF 16), proof of Theorem 4, eq. (6)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_MNLQC_Model

namespace AssortSearch.MNLQC

/-- **(6)** (proof of Theorem 4, p. 14): for `v_j = x > 0` and `c` differentiable on `(0, 1)`,
`h^m′(v_j) = numerator6 / (v_j + V_S)^2`, with `V_S = v_0 + ∑_{i∈S} v_i` and the numerator
written with per-variant margins (`m_j` in the first bracket, `m_i` in the sum). -/
theorem eq_6
    {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (hc_concave : ConcaveOn ℝ (Set.Icc 0 1) c) (hc_mono : MonotoneOn c (Set.Icc 0 1))
    (hj : j ∉ S)
    (hc_diff : DifferentiableOn ℝ c (Set.Ioo 0 1)) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (hm m c v v0 S j)
      (numerator6 m c v v0 S j x / (x + prefTotal v v0 S) ^ 2) x := by sorry

end AssortSearch.MNLQC
