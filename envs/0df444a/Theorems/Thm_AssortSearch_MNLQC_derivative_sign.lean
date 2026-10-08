-- Prove2me | Theorems.Thm_AssortSearch_MNLQC_derivative_sign
-- name    : AssortSearch.MNLQC.derivative_sign
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:41.855895+00:00
-- url     : https://prove2.me/theorems/776a4e3a-e652-40c6-a3ac-7ad4c53d45a6
-- title:
--   Sign pattern of $h^{m\prime}$: nonpositive, then nonnegative
-- statement:
--   Let $v_1,\dots,v_n > 0$, $v_0 > 0$, margins $m_1,\dots,m_n \in \mathbb R$, and an operational cost $c$ that is concave and increasing on $[0,1]$ and differentiable on $(0,1)$. Fix an assortment $S$ and $j \notin S$. Let $h^m(v_j) = \pi_j^m(v_j) - L^m(v_j)$ be the profit change from adding $j$ with preference $v_j$ under the MNL model without search.
--
--   Then $h^{m\prime}$ changes sign at most once, from nonpositive to nonnegative. Either
--
--   $$h^{m\prime}(v_j) \le 0 \quad \text{for all } v_j > 0,$$
--
--   or there is a threshold $a \ge 0$ such that
--
--   $$h^{m\prime}(v_j) \le 0 \ \text{ for } 0 < v_j < a, \qquad h^{m\prime}(v_j) \ge 0 \ \text{ for } v_j > a.$$
--
--   The paper derives this from (6) and the monotonicity of the numerator, and concludes from it that $h^m$ is quasi-convex.
--
--   **Formalization Note** The paper says "there is at most one $v_j$ such that $h^{m\prime}(v_j) = 0$". Read literally this is false when the numerator vanishes on a whole interval, for instance with $c(q) = aq + b$ linear and every margin equal to $a$, when $h^m$ is constant. The statement is therefore the single-crossing form, which is what the paper's argument shows. Differentiability of $c$ on $(0,1)$ is added because the paper differentiates $c$. Mathlib's `deriv` is used, and it is the true derivative at every $v_j > 0$ by (6).
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 14 (PDF 16), proof of Theorem 4, last two sentences

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_MNLQC_Model

namespace AssortSearch.MNLQC

/-- Proof of Theorem 4 (p. 14): the sign pattern of `h^m′`. Either `h^m′ ≤ 0` on all of
`(0, ∞)`, or there is a threshold `a ≥ 0` with `h^m′ ≤ 0` on `(0, a)` and `h^m′ ≥ 0` on
`(a, ∞)`. (The paper states "at most one `v_j` such that `h^m′(v_j) = 0`", which fails when
the numerator of (6) vanishes on an interval; this is the sign-change form its argument
proves.) -/
theorem derivative_sign
    {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (hc_concave : ConcaveOn ℝ (Set.Icc 0 1) c) (hc_mono : MonotoneOn c (Set.Icc 0 1))
    (hj : j ∉ S)
    (hc_diff : DifferentiableOn ℝ c (Set.Ioo 0 1)) :
    (∀ x : ℝ, 0 < x → deriv (hm m c v v0 S j) x ≤ 0) ∨
      ∃ a : ℝ, 0 ≤ a ∧
        (∀ x : ℝ, 0 < x → x < a → deriv (hm m c v v0 S j) x ≤ 0) ∧
        (∀ x : ℝ, a < x → 0 ≤ deriv (hm m c v v0 S j) x) := by sorry

end AssortSearch.MNLQC
