-- Prove2me | Theorems.Thm_DataDrivenRO_Marginal_var_pos_homog
-- name    : DataDrivenRO.Marginal.var_pos_homog
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:21:12.841955+00:00
-- url     : https://prove2.me/theorems/0c63225f-0c03-493c-bacc-c3906d5e58f9
-- title:
--   p. 10 — Value at Risk is positively homogeneous in v
-- statement:
--   Let $\mathbb P$ be a probability measure on $\mathbb R^d$ and $0<\delta<1$. For every $\mathbf w\in\mathbb R^d$ and every $c>0$,
--   $$\mathrm{VaR}^{\mathbb P}_\delta(c\,\mathbf w)=c\,\mathrm{VaR}^{\mathbb P}_\delta(\mathbf w),$$
--   where $\mathrm{VaR}^{\mathbb P}_\delta(\mathbf v)=\inf\{t:\mathbb P(\tilde{\mathbf u}^T\mathbf v\le t)\ge1-\delta\}$.
--
--   Positive homogeneity lets the proof of Theorem 7 rewrite $\mathrm{VaR}_{\epsilon/d}(v_i\mathbf e_i)$ as $v_i\mathrm{VaR}_{\epsilon/d}(\mathbf e_i)$ for $v_i>0$ and as $|v_i|\mathrm{VaR}_{\epsilon/d}(-\mathbf e_i)$ for $v_i<0$.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, §3.1, sentence after (6), p. 10

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

open MeasureTheory

namespace DataDrivenRO.Marginal

/-- p. 10: Value at Risk is positively homogeneous in `v`: `VaR^ℙ_δ(c v) = c VaR^ℙ_δ(v)` for `c > 0`. -/
theorem var_pos_homog {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P] (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (c : ℝ) (hc : 0 < c) (w : Fin d → ℝ) :
    VaR P δ (c • w) = c * VaR P δ w := by sorry

end DataDrivenRO.Marginal
