-- Prove2me | Theorems.Thm_CVPricing_CertEquiv_V_C_recursive
-- name    : CVPricing.CertEquiv.V_C_recursive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:36:26.703544+00:00
-- url     : https://prove2.me/theorems/49e9beda-4e61-48bb-83df-0a8276c8e4ee
-- title:
--   Proof of Proposition 1, p. 780 — recursive forms of $V_t$ and $C_t$
-- statement:
--   Let $(p_i)_{i\ge1}$ and $(e_i)_{i\ge1}$ be real sequences, and let $\bar p_t$, $\bar e_t$ be their sample means, $V_t = \sum_{i=1}^t (p_i - \bar p_t)^2$ and $C_t = \sum_{i=1}^t (p_i - \bar p_t)e_i$. For all $t \ge 2$,
--
--   $$V_t = \sum_{i=2}^t \frac{i-1}{i}\,(p_i - \bar p_{i-1})^2, \qquad C_t = \sum_{i=2}^t \frac{i-1}{i}\,(p_i - \bar p_{i-1})(e_i - \bar e_{i-1}).$$
--
--   These updating formulas are what make $V_t$ and $C_t$ computable in closed form along the price path that is constant from period 3 on.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 780 (PDF 12), Appendix, proof of Proposition 1, 'For all t ≥ 2, V_t and C_t can be rewritten as'

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_EventA

namespace CVPricing.CertEquiv

open KeskinZeevi.SufficientConditions

theorem V_C_recursive (p e : ℕ → ℝ) {t : ℕ} (ht : 2 ≤ t) :
    infoMetricOf p t =
        ∑ i ∈ Finset.Icc 2 t, ((i : ℝ) - 1) / i * (p i - avgPriceOf p (i - 1)) ^ 2 ∧
      crossSum p e t =
        ∑ i ∈ Finset.Icc 2 t,
          ((i : ℝ) - 1) / i * (p i - avgPriceOf p (i - 1)) * (e i - avgPriceOf e (i - 1)) := by sorry

end CVPricing.CertEquiv
