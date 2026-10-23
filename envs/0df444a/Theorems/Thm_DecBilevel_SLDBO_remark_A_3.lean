-- Prove2me | Theorems.Thm_DecBilevel_SLDBO_remark_A_3
-- name    : DecBilevel.SLDBO.remark_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:38.606606+00:00
-- url     : https://prove2.me/theorems/c1f4ff9f-e101-4b5d-919e-2f084b68725f
-- title:
--   Remark A.3, (32)–(33), p. 17 — successive differences of x and y
-- statement:
--   Under the setting of Lemma A.6, for every $k\ge0$
--
--   1. $$\sum_{i=1}^n\|x^{k+1}_i-x^k_i\|^2\le8\sum_{i=1}^n\|x^k_i-\bar x^k\|^2+4\alpha^2\sum_{i=1}^n\|t^k_{x,i}-\bar t^k_x\|^2+4n\alpha^2\|\bar d^k_x\|^2;$$
--   2. $$\sum_{i=1}^n\|y^{k+1}_i-y^k_i\|^2\le8\sum_{i=1}^n\|y^k_i-\bar y^k\|^2+4\beta^2\sum_{i=1}^n\|t^k_{y,i}-\bar t^k_y\|^2+4n\beta^2\|\bar d^k_y\|^2.$$
-- source:
--   Dong, Ma, Yang, Yin, A Single-Loop Algorithm for Decentralized Bilevel Optimization, arXiv:2311.08945v3, p. 17, Remark A.3, (32)–(33)

import Mathlib
import Definitions.Def_DecBilevel_SLDBO_Setting

namespace DecBilevel.SLDBO

theorem remark_A_3 {n p q : ℕ} (hn : 0 < n) (W : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (F f : Fin n → E p → E q → ℝ) (σ LF0 LF1 Lf1 Lf2 : ℝ) (α β η : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hη : 0 < η) (x0 : E p) (y0 v0 : E q)
    (hA21 : Assumption21 F f σ LF0 LF1 Lf1 Lf2) (hA22 : Assumption22 W ρ)
    (hv0 : ‖v0‖ ≤ rv σ LF0) (k : ℕ) :
    let s := run W F f α β η (rv σ LF0) x0 y0 v0
    (∑ i, ‖(s (k + 1)).x i - (s k).x i‖ ^ 2 ≤
      8 * ∑ i, ‖(s k).x i - avg (s k).x‖ ^ 2 +
      4 * α ^ 2 * ∑ i, ‖trX s k i - avg (trX s k)‖ ^ 2 +
      4 * n * α ^ 2 * ‖avg (dirX s k)‖ ^ 2) ∧
    (∑ i, ‖(s (k + 1)).y i - (s k).y i‖ ^ 2 ≤
      8 * ∑ i, ‖(s k).y i - avg (s k).y‖ ^ 2 +
      4 * β ^ 2 * ∑ i, ‖trY s k i - avg (trY s k)‖ ^ 2 +
      4 * n * β ^ 2 * ‖avg (dirY s k)‖ ^ 2) := by sorry

end DecBilevel.SLDBO
