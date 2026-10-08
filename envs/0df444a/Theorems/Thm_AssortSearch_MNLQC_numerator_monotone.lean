-- Prove2me | Theorems.Thm_AssortSearch_MNLQC_numerator_monotone
-- name    : AssortSearch.MNLQC.numerator_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:37.989973+00:00
-- url     : https://prove2.me/theorems/6c9a1ef8-a148-4943-86e4-5062f17abd22
-- title:
--   The numerator of (6) is nondecreasing in $v_j$
-- statement:
--   Let $v_1,\dots,v_n > 0$, $v_0 > 0$, margins $m_1,\dots,m_n \in \mathbb R$, and an operational cost $c$ that is concave and increasing on $[0,1]$ and differentiable on $(0,1)$. Fix an assortment $S$ and $j \notin S$, and let $V_S = v_0 + \sum_{i\in S} v_i$. Define the numerator of (6) as a function of the added variant's preference $v_j$:
--
--   $$\mathcal N(v_j) = \Big[m_j V_S - c'\Big(\tfrac{v_j}{v_j+V_S}\Big) V_S\Big] - \Big[\sum_{i\in S} m_i v_i - \sum_{i\in S} c'\Big(\tfrac{v_i}{v_j+V_S}\Big) v_i\Big].$$
--
--   Then $\mathcal N$ is nondecreasing on $(0,\infty)$:
--
--   $$0 < x \le y \implies \mathcal N(x) \le \mathcal N(y).$$
--
--   This is the step of the proof of Theorem 4 that says "the numerator is increasing in $v_j$". Together with (6), it controls the sign of $h^{m\prime}$.
--
--   **Formalization Note** The paper's "increasing" is formalized as nondecreasing (`MonotoneOn`). Strict increase fails when, for example, $c$ is linear, since the numerator is then constant. Differentiability of $c$ on $(0,1)$ is added because the numerator is written with $c'$ (Mathlib's `deriv c`). The domain is $(0,\infty)$ rather than $[0,\infty)$, because $c'(0)$ at the endpoint of $c$'s domain is not determined by the hypotheses. Margins are per-variant, as in the model; the paper's proof writes one common $m$.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 14 (PDF 16), proof of Theorem 4, the sentences following (6)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_MNLQC_Model

namespace AssortSearch.MNLQC

/-- Proof of Theorem 4 (p. 14): the numerator of (6) is nondecreasing in `v_j` on `(0, ∞)`
(the paper: "the numerator is increasing in `v_j`"), for `c` concave and differentiable on
`(0, 1)`. -/
theorem numerator_monotone
    {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (hc_concave : ConcaveOn ℝ (Set.Icc 0 1) c) (hc_mono : MonotoneOn c (Set.Icc 0 1))
    (hj : j ∉ S)
    (hc_diff : DifferentiableOn ℝ c (Set.Ioo 0 1)) :
    MonotoneOn (numerator6 m c v v0 S j) (Set.Ioi 0) := by sorry

end AssortSearch.MNLQC
