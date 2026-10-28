-- Prove2me | Theorems.Thm_EndoCredit_Baseline_alpha_plus_gt_one
-- name    : EndoCredit.Baseline.alpha_plus_gt_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:58.312997+00:00
-- url     : https://prove2.me/theorems/1e0952ed-bfb7-4f6c-ada4-6ac2d9d6ede3
-- title:
--   §3.2, p. 11 — the positive root α₊ of (2.7) exceeds one
-- statement:
--   Let $\alpha_+$ be the root of the quadratic specified after (2.7), whose leading coefficient is positive. Under the baseline standing conditions, it is the unique positive root and
--
--   $$\alpha_+>1.$$
--
--   This establishes the root and sign used in the formulas for the shadow-price level and the credit limit.
--
--   **Formalization Note** The standing conditions include $\hat\beta>0$ and positive quadratic leading coefficient, which the printed page leaves implicit.
-- source:
--   Choi, Koo, Lim & Yoo, Endogenous Credit, Business Cycle, and Portfolio Selection, SSRN 2560607, https://ssrn.com/abstract=2560607 (version of October 25, 2023), p. 7, (2.7) and quadratic defining α₊; p. 11, §3.2, 'In particular, since α₊ > 1'

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Model

namespace EndoCredit.Baseline

/-- The root specified after (2.7) is the sole positive root and exceeds one. -/
theorem alpha_plus_gt_one (p : Params) (hp : p.Standing) :
    1 < alphaPlus p ∧
    quadA p * alphaPlus p * (alphaPlus p - 1) +
      (betaHat p - rI p) * alphaPlus p - betaHat p = 0 ∧
    ∀ a : ℝ, 0 < a →
      quadA p * a * (a - 1) + (betaHat p - rI p) * a - betaHat p = 0 →
      a = alphaPlus p := by sorry

end EndoCredit.Baseline
