-- Prove2me | Theorems.Thm_AddLogReg_Discrete_neg_y_f_eq
-- name    : AddLogReg.Discrete.neg_y_f_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:52.721119+00:00
-- url     : https://prove2.me/theorems/a14d5faf-2638-4729-848d-bc92b36403f2
-- title:
--   Proof of Result 1, p. 347 — −yf(x) = 2 × 1_{[y≠f(x)]} − 1, so e^{−cf(x)y} = e^{−c} exp(2c 1_{[y≠f(x)]})
-- statement:
--   For $y, s \in \{-1, 1\}$,
--   $$-ys = 2 \times 1_{[y \neq s]} - 1,$$
--   and consequently, for every real $c$,
--   $$e^{-csy} = e^{-c} \exp\big(2c \cdot 1_{[y \neq s]}\big).$$
--
--   Applied with $s = f(x)$ and the line-search coefficient $c = \frac12\log((1-\mathrm{err})/\mathrm{err})$, so that $2c = \log((1-\mathrm{err})/\mathrm{err})$, this shows that the population weight update $w(x, y) \leftarrow w(x, y) e^{-cf(x)y}$ differs from Discrete AdaBoost's update $w(x, y) \leftarrow w(x, y)\exp(\log((1-\mathrm{err})/\mathrm{err})\, 1_{[y \neq f(x)]})$ only by the constant factor $e^{-c}$, which renormalization removes.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 347, proof of Result 1, last two displays

import Mathlib
import Definitions.Def_AddLogReg_Discrete_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Discrete

/-- Proof of Result 1, p. 347: for `y, s ∈ {−1, 1}`, `−ys = 2 × 1_{[y ≠ s]} − 1`; hence for every
real `c` the weight factor `e^{−csy}` equals `e^{−c} · exp(2c · 1_{[y ≠ s]})`. -/
theorem neg_y_f_eq (y s : ℝ) (hy : y = 1 ∨ y = -1) (hs : s = 1 ∨ s = -1) :
    -(y * s) = 2 * (if y ≠ s then 1 else 0) - 1 ∧
      ∀ c : ℝ, Real.exp (-(c * s * y)) =
        Real.exp (-c) * Real.exp (2 * c * (if y ≠ s then 1 else 0)) := by sorry

end AddLogReg.Discrete
