-- Prove2me | Theorems.Thm_CVPricing_CertEquiv_V_C_closed_forms
-- name    : CVPricing.CertEquiv.V_C_closed_forms
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:36:43.463765+00:00
-- url     : https://prove2.me/theorems/fb361537-e22a-4df4-b039-d5275c487567
-- title:
--   Proof of Proposition 1, pp. 780–781 — closed forms of $\bar p_i$, $V_t$, $C_t$ when $p_3 = \dots = p_t = p_h$
-- statement:
--   Let $p_h \in \mathbb R$, let $(p_i)_{i\ge1}$ and $(e_i)_{i\ge1}$ be real sequences and $t \ge 2$, and suppose $p_i = p_h$ for all $i = 3, \dots, t$. Then
--
--   1. $\bar p_i = p_h - \dfrac{2p_h - p_1 - p_2}{i}$ for $3 \le i \le t$;
--   2. $V_t = V_2 + (2p_h - p_1 - p_2)^2\big(\tfrac12 - t^{-1}\big)$;
--   3. $C_t = C_2 + (2p_h - p_1 - p_2)(\bar e_t - \bar e_2)$,
--
--   where $V_2 = \tfrac12 (p_2 - p_1)^2$ and $C_2 = \tfrac12 (p_2 - p_1)(e_2 - e_1)$, and $\bar p_t$, $\bar e_t$, $V_t$, $C_t$ are as in `CVPricing.CertEquiv.V_C_recursive`.
--
--   With these formulas, the condition that the next certainty equivalent price is again $p_h$ becomes an explicit condition on $e_1, e_2$ and $\bar e_t$, which is the shape of the event $A$.
--
--   **Formalization Note** $V_2$ and $C_2$ are written out explicitly in the conclusion.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 780 (PDF 12), Appendix, proof of Proposition 1, Case t ≥ 3 (formula for p̄_i); p. 781 (PDF 13), the closed forms of V_t and C_t

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_EventA

namespace CVPricing.CertEquiv

open KeskinZeevi.SufficientConditions

theorem V_C_closed_forms (ph : ℝ) (p e : ℕ → ℝ) {t : ℕ} (ht : 2 ≤ t)
    (hph : ∀ i : ℕ, 3 ≤ i → i ≤ t → p i = ph) :
    (∀ i : ℕ, 3 ≤ i → i ≤ t → avgPriceOf p i = ph - (2 * ph - p 1 - p 2) / i) ∧
      infoMetricOf p t =
        (1 / 2) * (p 2 - p 1) ^ 2 + (2 * ph - p 1 - p 2) ^ 2 * (1 / 2 - (t : ℝ)⁻¹) ∧
      crossSum p e t =
        (1 / 2) * (p 2 - p 1) * (e 2 - e 1) +
          (2 * ph - p 1 - p 2) * (avgPriceOf e t - avgPriceOf e 2) := by sorry

end CVPricing.CertEquiv
