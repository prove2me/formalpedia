-- Prove2me | Theorems.Thm_FlexLearning_Threshold_proposition_1
-- name    : FlexLearning.Threshold.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:01.358846+00:00
-- url     : https://prove2.me/theorems/4aa2406d-b39e-4d81-b099-804931fe3588
-- title:
--   Proposition 1, p. 12 — at the break-even cost of flexibility, V_F ≥ V_N for margins ≤ ζ and V_F ≤ V_N above ζ (ξ = 0, x = 0)
-- statement:
--   Consider the two-product, two-period capacity model with second-period demand equal to first-period demand ($\xi = 0$) and first-period demands independent and uniform on $[0, U]$ ($x = 0$, $U > 0$). Let $p$ be the common price, $c$ the dedicated unit cost and $c_F$ the flexible unit cost, with $0 \le c < p$ and $c \le c_F < p$, and suppose $c_F$ is a break-even cost of flexibility, $\bar\pi_F(c_F) = \bar\pi_N$ (Eq. (8)). Write $V_N$ and $V_F(c_F)$ for the optimal two-period profits of the non-flexible and the flexible system.
--
--   Then there is a profit-margin threshold $\zeta \in (0,1)$, the same for all such $p, c, c_F, U$, such that
--   $$\frac{p-c}{p} \le \zeta \implies V_F(c_F) \ge V_N, \qquad \frac{p-c}{p} > \zeta \implies V_F(c_F) \le V_N.$$
--
--   At the break-even cost the two systems have the same static profit, so the comparison isolates the **learning benefits of flexibility** $V_F(\tilde c_F) - V_N$, Eq. (14): for low and moderate margins the flexible system learns more from censored sales. The paper reports $\zeta \approx 0.5904$.
--
--   **Formalization Note** $\xi = 0$ is built into the model. Added: $U > 0$, $0 \le c < p$, and $c \le c_F < p$ (the sets $A$, $B$ of the proof, p. A7; the break-even cost lies there). The threshold is required to lie strictly between 0 and 1, which excludes a threshold under which one half of the claim is vacuous; the paper's value is $0.5904$.
-- source:
--   Chod, Markakis & Trichakis, On the Learning Benefits of Resource Flexibility, SSRN preprint 3212177 (version of December 6, 2019), p. 12 (PDF 12), Proposition 1; proof pp. A3–A8 (PDF 36–41)

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model

namespace FlexLearning.Threshold

theorem proposition_1 :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧
      ∀ p c U cF : ℝ, 0 ≤ c → c < p → 0 < U → c ≤ cF → cF < p →
        IsBreakEven p c 0 U cF →
        ((p - c) / p ≤ ζ → VN p c 0 U ≤ VF p c 0 U cF) ∧
        (ζ < (p - c) / p → VF p c 0 U cF ≤ VN p c 0 U) := by sorry

end FlexLearning.Threshold
