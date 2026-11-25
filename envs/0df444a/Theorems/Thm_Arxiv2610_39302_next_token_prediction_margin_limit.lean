-- Prove2me | Theorems.Thm_Arxiv2610_39302_next_token_prediction_margin_limit
-- name    : Arxiv2610_39302.next_token_prediction_margin_limit
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T03:06:48.200859+00:00
-- url     : https://prove2.me/theorems/b892a417-a088-474f-a2ae-3ab1ec1f8871
-- title:
--   Proposition 4 (ii) and eq. (6): the temperature-scaled next-token loss tends to the margin
-- statement:
--   Let a context be embedded by $h\in\mathbb{R}^k$ and the tokens $v$ of a finite nonempty vocabulary $V$ by vectors $w_v\in\mathbb{R}^k$, and let $A(h)=\log\sum_ve^{\langle h,w_v\rangle}$. Then for every target token $y$:
--
--   1. (eq. 6) the next-token loss with a linear softmax head is
--   $$-\log\frac{e^{\langle h,w_y\rangle}}{\sum_ve^{\langle h,w_v\rangle}}=-\langle h,w_y\rangle+A(h),$$
--   where $A$ does not depend on $y$;
--   2. $tA(h/t)\to\max_v\langle h,w_v\rangle$ as $t\to0^+$;
--   3. the temperature-scaled loss tends to the margin: $t\cdot\mathrm{loss}(h/t,y)\to\max_v\langle h,w_v\rangle-\langle h,w_y\rangle$ as $t\to0^+$;
--   4. the margin is nonnegative, and it vanishes if and only if the target attains the maximal logit.
--
--   **Formalization Note** The temperature $t$ tends to $0$ from above.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), claim c012; Section 2.4, Proposition 4, eq. (6) and part (ii), PDF p. 6; proof in Appendix A.5, PDF p. 23

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

namespace Arxiv2610_39302

theorem next_token_prediction_margin_limit {V : Type*} [Fintype V] [Nonempty V] {k : ℕ}
    (w : V → Fin k → ℝ) (h : Fin k → ℝ) (y : V) :
    ntpLoss w h y = -(h ⬝ᵥ w y) + ntpAntiCollapse w h ∧
    Tendsto (fun t : ℝ => t * ntpAntiCollapse w (fun i => h i / t)) (𝓝[>] 0)
      (𝓝 (⨆ v, h ⬝ᵥ w v)) ∧
    Tendsto (fun t : ℝ => t * ntpLoss w (fun i => h i / t) y) (𝓝[>] 0)
      (𝓝 ((⨆ v, h ⬝ᵥ w v) - h ⬝ᵥ w y)) ∧
    0 ≤ (⨆ v, h ⬝ᵥ w v) - h ⬝ᵥ w y ∧
    ((⨆ v, h ⬝ᵥ w v) - h ⬝ᵥ w y = 0 ↔ ∀ v, h ⬝ᵥ w v ≤ h ⬝ᵥ w y) := by sorry

end Arxiv2610_39302
