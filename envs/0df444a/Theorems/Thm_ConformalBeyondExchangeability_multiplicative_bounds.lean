-- Prove2me | Theorems.Thm_ConformalBeyondExchangeability_multiplicative_bounds
-- name    : ConformalBeyondExchangeability.multiplicative_bounds
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:53:06.554181+00:00
-- url     : https://prove2.me/theorems/c5725f20-0e09-49ba-b9f5-70157ca9b1f4
-- title:
--   Theorem 6: multiplicative bounds under Huber contamination
-- statement:
--   Let $Z_1,\dots,Z_{n+1}$ be independent with laws $\mu_1,\dots,\mu_{n+1}$ on $\mathcal X\times\mathbb R$. Let $\mathcal A$ be an algorithm that treats its input points symmetrically, let $w_1,\dots,w_n\in[0,1]$ with $w_1+\dots+w_n>0$, let $\bar w_i=w_i/(w_1+\dots+w_n)$, and let $\alpha\in(0,1)$. Write $\Delta=\sum_{i=1}^n\bar w_i\,\mathsf d_{\mathrm{mix}}(Z_i,Z_{n+1})$.
--
--   1. If the residual map $z\mapsto R(z)$ is measurable, the nonexchangeable full conformal set for a symmetric algorithm (eq. (12)) satisfies
--   $$P\{Y_{n+1}\notin\hat C_n(X_{n+1})\}\le\frac{\alpha}{1-\Delta}.$$
--   This includes nonexchangeable split conformal (eq. (11)) as the special case of an algorithm that returns a fixed function.
--   2. If the leave-two-out residual matrix $z\mapsto R_{\mathrm{jack+}}(z)$ is measurable, the nonexchangeable jackknife+ interval for a symmetric algorithm (eq. (33)) satisfies
--   $$P\{Y_{n+1}\notin\hat C_n(X_{n+1})\}\le\frac{2\alpha}{1-\Delta}.$$
--
--   Under an $\epsilon$-Huber contamination model the miscoverage inflates by at most the factor $1/(1-\epsilon)$.
--
--   **Formalization Note** The bounds are stated in $[0,\infty]$ with $x/0=+\infty$ for $x>0$, so the case $\Delta=1$, where the right side is $+\infty$, is included. Independence is the product form of the joint law.
-- source:
--   Barber, Candès, Ramdas and Tibshirani, Conformal prediction beyond exchangeability, arXiv:2202.13415v5 (2023), Appendix C, Theorem 6, eqs. (12), (33), (36), p. 41; proof in Appendix E.5, pp. 53-54

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory

namespace ConformalBeyondExchangeability

theorem multiplicative_bounds {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Fin (n + 1) → Measure (X × ℝ)) [∀ i, IsProbabilityMeasure (μ i)]
    (alg : Alg X) (halg : IsSymmetric alg)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (hwpos : 0 < ∑ i, w i)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (Measurable (symResiduals (n := n) alg) →
      Measure.pi μ {z | (z (Fin.last n)).2 ∉ symFullSet alg w α z} ≤
        ENNReal.ofReal α / ENNReal.ofReal (1 - mixTerm μ w)) ∧
    (Measurable (symJackResiduals (n := n) alg) →
      Measure.pi μ {z | (z (Fin.last n)).2 ∉ symJackInterval alg w α z} ≤
        ENNReal.ofReal (2 * α) / ENNReal.ofReal (1 - mixTerm μ w)) := by sorry

end ConformalBeyondExchangeability
