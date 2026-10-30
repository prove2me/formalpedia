-- Prove2me | Theorems.Thm_DecBilevel_SLDBO_remark_A_1
-- name    : DecBilevel.SLDBO.remark_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:27.604426+00:00
-- url     : https://prove2.me/theorems/abaac2c2-0849-4795-b347-e878f3b9aa75
-- title:
--   Remark A.1, (22)–(23), p. 15 — consensus contraction of x and y
-- statement:
--   Under the setting of Lemma A.3 (Algorithm 1 from BOX 1, Assumptions 2.1 and 2.2, any $\alpha,\beta,\eta>0$), for every $k\ge0$
--
--   1. $$\sum_{i=1}^n\|x^{k+1}_i-\bar x^{k+1}\|^2\le\rho\sum_{i=1}^n\|x^k_i-\bar x^k\|^2+\frac{\rho^2\alpha^2}{1-\rho}\sum_{i=1}^n\|t^k_{x,i}-\bar t^k_x\|^2;$$
--   2. $$\sum_{i=1}^n\|y^{k+1}_i-\bar y^{k+1}\|^2\le\rho\sum_{i=1}^n\|y^k_i-\bar y^k\|^2+\frac{\rho^2\beta^2}{1-\rho}\sum_{i=1}^n\|t^k_{y,i}-\bar t^k_y\|^2.$$
--
--   These are the unprojected analogues of (21).
-- source:
--   Dong, Ma, Yang, Yin, A Single-Loop Algorithm for Decentralized Bilevel Optimization, arXiv:2311.08945v3, p. 15, Remark A.1, (22)–(23)

import Mathlib
import Definitions.Def_DecBilevel_SLDBO_Setting

namespace DecBilevel.SLDBO

theorem remark_A_1 {n p q : ℕ} (hn : 0 < n) (W : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (F f : Fin n → E p → E q → ℝ) (σ LF0 LF1 Lf1 Lf2 : ℝ) (α β η : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hη : 0 < η) (x0 : E p) (y0 v0 : E q)
    (hA21 : Assumption21 F f σ LF0 LF1 Lf1 Lf2) (hA22 : Assumption22 W ρ)
    (hv0 : ‖v0‖ ≤ rv σ LF0) (k : ℕ) :
    let s := run W F f α β η (rv σ LF0) x0 y0 v0
    (∑ i, ‖(s (k + 1)).x i - avg (s (k + 1)).x‖ ^ 2 ≤
      ρ * ∑ i, ‖(s k).x i - avg (s k).x‖ ^ 2 +
      ρ ^ 2 * α ^ 2 / (1 - ρ) * ∑ i, ‖trX s k i - avg (trX s k)‖ ^ 2) ∧
    (∑ i, ‖(s (k + 1)).y i - avg (s (k + 1)).y‖ ^ 2 ≤
      ρ * ∑ i, ‖(s k).y i - avg (s k).y‖ ^ 2 +
      ρ ^ 2 * β ^ 2 / (1 - ρ) * ∑ i, ‖trY s k i - avg (trY s k)‖ ^ 2) := by sorry

end DecBilevel.SLDBO
