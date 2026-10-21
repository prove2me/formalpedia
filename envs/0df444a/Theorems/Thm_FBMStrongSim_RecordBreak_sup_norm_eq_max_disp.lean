-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_sup_norm_eq_max_disp
-- name    : FBMStrongSim.RecordBreak.sup_norm_eq_max_disp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:33.777536+00:00
-- url     : https://prove2.me/theorems/8ae94ebc-5039-4126-b9ef-9b9e36aaec88
-- title:
--   Display after (3.1), p. 8 — ‖B^H_k − B^H_{k−1}‖∞ = max_j |a^k_j − b^k_j|
-- statement:
--   Let $x:\mathbb R\to\mathbb R$ be any function and let $x_n$ denote its piecewise-linear interpolation on the dyadic grid $D_n=\{i/2^n:0\le i\le 2^n\}$. For every level $k\ge1$, with $a^k_j=x(t^k_{2j+1})$ and $b^k_j=\tfrac12(x(t^{k-1}_j)+x(t^{k-1}_{j+1}))$,
--   $$\sup_{t\in[0,1]}|x_k(t)-x_{k-1}(t)|=\max_{0\le j\le 2^{k-1}-1}|a^k_j-b^k_j|,$$
--   and the supremum is attained.
--
--   This identity turns the sup-norm increment of the dyadic expansion into a finite maximum of midpoint displacements, which is what the record-breaker condition and Theorem 3.1 control.
--
--   **Formalization Note** The statement says that the right-hand side is the greatest element of $\{|x_k(t)-x_{k-1}(t)|:t\in[0,1]\}$, so no real supremum (which would default to $0$ on unbounded sets) is used.
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 8, display after (3.1)

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FBMStrongSim.RecordBreak

/-- Display after (3.1), p. 8: for every path `x` and every level `k ≥ 1`,
`‖B_k − B_{k−1}‖∞ = max_{0 ≤ j ≤ 2^{k−1}−1} |a^k_j − b^k_j|`, the sup over `[0,1]` being
attained. -/
theorem sup_norm_eq_max_disp (x : ℝ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    IsGreatest ((fun t => |interp x k t - interp x (k - 1) t|) '' Set.Icc (0 : ℝ) 1)
      (maxDisp x k) := by sorry

end FBMStrongSim.RecordBreak
