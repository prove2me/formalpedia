-- Prove2me | Theorems.Thm_CandesTao_LowerBound_one_sub_exp_neg_gt
-- name    : CandesTao.LowerBound.one_sub_exp_neg_gt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:44:55.761983+00:00
-- url     : https://prove2.me/theorems/9878bd35-3caa-48da-b3b0-3aff95155906
-- title:
--   Section II — $1 - e^{-x} > x - x^2/2$ for $x > 0$
-- statement:
--   For every real $x > 0$,
--
--   $$1 - e^{-x} > x - \frac{x^2}{2}.$$
--
--   This is the elementary inequality from which Candès and Tao derive the easier-to-read condition (I.21) from (I.20) in Theorem 1.7, applied with $x = \frac{\mu_0 r}{n}\log\left(\frac{n}{2\delta}\right)$.
--
--   **Formalization Note.** The paper prints the range as "whenever $x \ge 0$". At $x = 0$ both sides equal $0$, so the strict inequality fails there; this item states the corrected range $x > 0$. In the paper's application, $x = \frac{\mu_0 r}{n}\log\left(\frac{n}{2\delta}\right) > 0$ because $n/(2\delta) > 1$, so the correction does not affect Theorem 1.7.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2060, Section II, last sentence ('(I.21) follows from 1 − e^{−x} > x − x²/2 whenever x ≥ 0')

import Mathlib.Analysis.SpecialFunctions.Exp

namespace CandesTao.LowerBound

theorem one_sub_exp_neg_gt (x : ℝ) (hx : 0 < x) :
    1 - Real.exp (-x) > x - x ^ 2 / 2 := by sorry

end CandesTao.LowerBound
