-- Prove2me | Theorems.Thm_DecBilevel_SLDBO_remark_A_2
-- name    : DecBilevel.SLDBO.remark_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:36.309006+00:00
-- url     : https://prove2.me/theorems/5ae29496-e10f-4b5d-aff7-e9e63e47fd0a
-- title:
--   Remark A.2, (26)–(27), p. 15 — tracker consensus contraction for v and y
-- statement:
--   Under the setting of Lemma A.4, for every $k\ge0$
--
--   1. $$\sum_{i=1}^n\|t^{k+1}_{v,i}-\bar t^{k+1}_v\|^2\le\rho\sum_{i=1}^n\|t^k_{v,i}-\bar t^k_v\|^2+\frac1{1-\rho}\sum_{i=1}^n\|d^{k+1}_{v,i}-d^k_{v,i}\|^2;$$
--   2. $$\sum_{i=1}^n\|t^{k+1}_{y,i}-\bar t^{k+1}_y\|^2\le\rho\sum_{i=1}^n\|t^k_{y,i}-\bar t^k_y\|^2+\frac1{1-\rho}\sum_{i=1}^n\|d^{k+1}_{y,i}-d^k_{y,i}\|^2.$$
-- source:
--   Dong, Ma, Yang, Yin, A Single-Loop Algorithm for Decentralized Bilevel Optimization, arXiv:2311.08945v3, p. 15, Remark A.2, (26)–(27)

import Mathlib
import Definitions.Def_DecBilevel_SLDBO_Setting

namespace DecBilevel.SLDBO

theorem remark_A_2 {n p q : ℕ} (hn : 0 < n) (W : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (F f : Fin n → E p → E q → ℝ) (σ LF0 LF1 Lf1 Lf2 : ℝ) (α β η : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hη : 0 < η) (x0 : E p) (y0 v0 : E q)
    (hA21 : Assumption21 F f σ LF0 LF1 Lf1 Lf2) (hA22 : Assumption22 W ρ)
    (hv0 : ‖v0‖ ≤ rv σ LF0) (k : ℕ) :
    let s := run W F f α β η (rv σ LF0) x0 y0 v0
    (∑ i, ‖trV s (k + 1) i - avg (trV s (k + 1))‖ ^ 2 ≤
      ρ * ∑ i, ‖trV s k i - avg (trV s k)‖ ^ 2 +
      1 / (1 - ρ) * ∑ i, ‖dirV s (k + 1) i - dirV s k i‖ ^ 2) ∧
    (∑ i, ‖trY s (k + 1) i - avg (trY s (k + 1))‖ ^ 2 ≤
      ρ * ∑ i, ‖trY s k i - avg (trY s k)‖ ^ 2 +
      1 / (1 - ρ) * ∑ i, ‖dirY s (k + 1) i - dirY s k i‖ ^ 2) := by sorry

end DecBilevel.SLDBO
