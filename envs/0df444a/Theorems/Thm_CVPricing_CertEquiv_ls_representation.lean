-- Prove2me | Theorems.Thm_CVPricing_CertEquiv_ls_representation
-- name    : CVPricing.CertEquiv.ls_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:36:27.573904+00:00
-- url     : https://prove2.me/theorems/a64870aa-b4e0-41ea-bdbd-417ac65a5c60
-- title:
--   Proof of Proposition 1, p. 780 — $(\hat a_{0t}, \hat a_{1t}) = (a_0^{(0)}, a_1^{(0)}) + (\bar e_t - \bar p_t C_t/V_t,\ C_t/V_t)$
-- statement:
--   Let $(p_i)_{i\ge1}$ be prices with $p_1 \ne p_2$, let $(e_i)_{i\ge1}$ be noise values, and let $d_i = a_0 + a_1 p_i + e_i$. For every $t \ge 2$, the least squares estimates $(\hat a_{0t}, \hat a_{1t})$ computed from $(p_i, d_i)_{i \le t}$ satisfy
--
--   $$\begin{pmatrix}\hat a_{0t}\\ \hat a_{1t}\end{pmatrix} = \begin{pmatrix} a_0\\ a_1\end{pmatrix} + \begin{pmatrix}\bar e_t - \bar p_t C_t / V_t \\ C_t / V_t\end{pmatrix},$$
--
--   where $\bar p_t, \bar e_t$ are the sample means, $C_t = \sum_{i=1}^t (p_i - \bar p_t)e_i$ and $V_t = \sum_{i=1}^t (p_i - \bar p_t)^2$.
--
--   This expresses the estimation error of ordinary least squares through the two scalar sums $C_t$ and $V_t$, which the proof of Proposition 1 then controls.
--
--   **Formalization Note** The paper states the representation in the case $p_3 = \dots = p_t = p_h$ of its induction; it holds for every price sequence with $p_1 \ne p_2$ (which makes $V_t > 0$), and is stated in that generality. The estimate is the referenced `lsEstimateOf`, the solution of the normal equations (4).
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 780 (PDF 12), Appendix, proof of Proposition 1, Case t ≥ 3, the display of the least squares estimates

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_EventA

namespace CVPricing.CertEquiv

open KeskinZeevi.SufficientConditions

theorem ls_representation (a₀ a₁ : ℝ) (p e : ℕ → ℝ) (hp : p 1 ≠ p 2) {t : ℕ} (ht : 2 ≤ t) :
    lsEstimateOf p (fun s => a₀ + a₁ * p s + e s) t =
      (a₀ + (avgPriceOf e t - avgPriceOf p t * crossSum p e t / infoMetricOf p t),
        a₁ + crossSum p e t / infoMetricOf p t) := by sorry

end CVPricing.CertEquiv
