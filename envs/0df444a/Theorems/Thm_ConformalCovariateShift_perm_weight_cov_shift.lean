-- Prove2me | Theorems.Thm_ConformalCovariateShift_perm_weight_cov_shift
-- name    : ConformalCovariateShift.perm_weight_cov_shift
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T02:24:27.756199+00:00
-- url     : https://prove2.me/theorems/ce3865e8-ec65-4dfb-a29b-ecf80bd1620d
-- title:
--   Section 3.5: the weights (15) reduce to the weights (7) under covariate shift
-- statement:
--   Let $w:\mathbb{R}^d\to\mathbb{R}$, let $Z_i=(X_i,Y_i)$, $i=1,\dots,n$, be points of $\mathbb{R}^d\times\mathbb{R}$ and let $(x,y)\in\mathbb{R}^d\times\mathbb{R}$. Take the weight functions $w_i\equiv1$ for $i=1,\dots,n$ and $w_{n+1}((x',y'))=w(x')$. Then the weights (15) evaluated at $Z_1,\dots,Z_n,(x,y)$ are the covariate-shift weights (7):
--
--   $$p_i^w\big(Z_1,\dots,Z_n,(x,y)\big)=p_i^w(x),\qquad i=1,\dots,n+1,$$
--
--   that is, $p_i^w=w(X_i)/(\sum_{j=1}^nw(X_j)+w(x))$ for $i\le n$ and $p_{n+1}^w=w(x)/(\sum_{j=1}^nw(X_j)+w(x))$.
--
--   This computation turns the combinatorial weights of Theorem 2 into the weights of Corollary 1.
--
--   **Formalization Note** The identity is stated for every real function $w$. When $\sum_{j=1}^nw(X_j)+w(x)=0$ both sides are $0$ under Lean's convention $a/0=0$.
-- source:
--   Tibshirani, Barber, Candès and Ramdas, Conformal Prediction Under Covariate Shift, arXiv:1904.06019v3 (2019), Section 3.5, proof of Corollary 1, display after the first paragraph, p. 14

import Mathlib
import Definitions.Def_ConformalCovariateShift_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalCovariateShift

theorem perm_weight_cov_shift {d n : ℕ} (w : (Fin d → ℝ) → ℝ) (data : Fin n → DataPt d)
    (x : Fin d → ℝ) (y : ℝ) :
    permWeight (fun j (z : DataPt d) => if j = Fin.last n then w z.1 else 1)
        (withTest data (x, y)) =
      covShiftWeights w (fun i => (data i).1) x := by sorry

end ConformalCovariateShift
