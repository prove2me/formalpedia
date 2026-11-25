-- Prove2me | Theorems.Thm_ConformalCovariateShift_quantile_with_inf_iff
-- name    : ConformalCovariateShift.quantile_with_inf_iff
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T02:21:37.065897+00:00
-- url     : https://prove2.me/theorems/b24b1d65-0734-48c6-999f-0f8bd3c8820b
-- title:
--   Eq. (2): replacing the test score by $\infty$ does not change the comparison
-- statement:
--   Let $n\ge0$, let $v_1,\dots,v_{n+1}\in\mathbb{R}$ and let $\beta\in(0,1)$. Then
--
--   $$v_{n+1}\le\mathrm{Quantile}\big(\beta;v_{1:n}\cup\{\infty\}\big)\iff v_{n+1}\le\mathrm{Quantile}\big(\beta;v_{1:(n+1)}\big).$$
--
--   This is the deterministic step (2) in the proof of Lemma 1: replacing the test value by $\infty$ in the empirical distribution does not change whether the test value lies below the level-$\beta$ quantile. The proof of Lemma 3 invokes a weighted analogue ("as in (2)"), with the weights $p^w$ in place of $1/(n+1)$; that analogue is not part of this statement.
-- source:
--   Tibshirani, Barber, Candès and Ramdas, Conformal Prediction Under Covariate Shift, arXiv:1904.06019v3 (2019), Section 1.1, proof of Lemma 1, eq. (2), p. 2

import Mathlib
import Definitions.Def_ConformalCovariateShift_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalCovariateShift

theorem quantile_with_inf_iff {n : ℕ} (v : Fin (n + 1) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (v (Fin.last n) : EReal) ≤ quantileWithInf β v ↔ (v (Fin.last n) : EReal) ≤ empQuantile β v := by sorry

end ConformalCovariateShift
