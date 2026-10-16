-- Prove2me | Theorems.Thm_AccelVI_MVC_alpha_eq_one_add_beta
-- name    : AccelVI.MVC.alpha_eq_one_add_beta
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:27.637098+00:00
-- url     : https://prove2.me/theorems/d23f8fe5-8e58-4cc4-87cc-7c3deff3446a
-- title:
--   Proof of Lemma B.1, p. 21 — for the step sizes (4.2), α = 1 + β
-- statement:
--   Let $\lambda \in (0,1)$ and let $\alpha, \beta$ be the constant step sizes (4.2) of Momentum Value Computation,
--   $$\alpha = \frac{2}{1 + \sqrt{1-\lambda^2}}, \qquad \beta = \frac{1 - \sqrt{1-\lambda^2}}{1 + \sqrt{1-\lambda^2}}.$$
--   Then
--   $$\alpha = 1 + \beta .$$
--
--   This identity makes the coefficient $1 - \alpha + \beta$ of $v_s$ vanish in the expanded M-VC recursion, which is what turns the iteration into the linear recursion $x_s = B_\pi x_{s-1} + b_\pi$ of Lemma B.1.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 21, proof of Lemma B.1, first paragraph

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_MVC_Setting

namespace AccelVI.MVC

/-- Proof of Lemma B.1, p. 21: for α, β tuned as in (4.2), α = 1 + β. -/
theorem alpha_eq_one_add_beta (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    alphaMVC lam = 1 + betaMVC lam := by sorry

end AccelVI.MVC
