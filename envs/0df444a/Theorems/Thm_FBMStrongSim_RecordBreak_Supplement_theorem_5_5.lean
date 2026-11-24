-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_Supplement_theorem_5_5
-- name    : FBMStrongSim.RecordBreak.Supplement.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:36:09.046329+00:00
-- url     : https://prove2.me/theorems/c115c4e4-9032-4fb1-9a9a-ea2c9beb477a
-- title:
--   Theorem 5.5 — (corrected: zero-norm envelopes) Uniform Euler rate on every level
-- statement:
--   Let $d,h\ge1$, $1/2<\alpha\le1$, $C>0$, $x:[0,1]\to\mathbb R^h$ be $\alpha$-Hölder with constant $C$, and let $f$ be bounded $C^2$ with entrywise envelopes $F_0,F_1>0$ and $F_2\ge0$. For every initial value $y_0$ and every Young solution $y$, the left-point Euler scheme with its piecewise constant extension satisfies, for every $n\in\mathbb N$ and $t\in[0,1]$,
--   $$|y_n(t)-y(t)|\le(\Upsilon_{\lceil(4\zeta)^{1/\alpha}\rceil}+G_1^*)\Delta_n^{2\alpha-1},\qquad\Delta_n=2^{-n}.$$
--   The constants and recurrence are computed in YoungConstants using the printed $L,G_1,\zeta,\upsilon$ and $\Upsilon$ formulas. The demonstrated local correction of Lemma 5.8 is not propagated into this separate target. The theorem covers every Young solution and all discretization levels; it assumes neither an error bound nor a lower threshold on $n$.
--
--   Differences from the source:
--   - reading: absolute values of vectors, matrices and derivatives → maximum vector norm and maximum absolute derivative entries; reason: the explicit norm convention planned in the brief, making all dimension factors checkable
--   - correction: constants evaluated at the exact derivative norms, including zero norms → F0,F1 are positive uniform entrywise envelopes and F2 is a nonnegative uniform entrywise envelope; reason: the printed ω divides by L=0 for constant fields; for α<1 the printed G1* is also zero when ∇f=0 although a nonzero constant field has a nonconstant solution; see DISPROOF.md; every bounded C² field admits these envelopes
--   - encoding: piecewise constant Euler extension (5.5) → the left grid value on each half-open cell and the final grid value at t=1; reason: this makes the otherwise unstated endpoint convention explicit, with no loss of times or levels
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 31, Theorem 5.5

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_HolderModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_YoungModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_EulerModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_GridHolderModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_YoungConstants

namespace FBMStrongSim.RecordBreak.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Theorem 5.5 (p.31), every n including coarse grids, with its printed constants. -/
theorem theorem_5_5 {d h : ℕ} (hd : 0 < d) (hh : 0 < h) {alpha C F0 F1 F2 : ℝ}
    (ha : 1 / 2 < alpha) (ha1 : alpha ≤ 1) (hC : 0 < C)
    {f : Field d h} (hf : CoefficientBounds f F0 F1 F2)
    {x : ℝ → Vec h} (hx : HolderBound alpha C x)
    (y0 : Vec d) {y : ℝ → Vec d} (hy : YoungSolution alpha f x y0 y) :
    ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖euler f x y0 n t - y t‖ ≤
        eulerConstant d h alpha C F0 F1 F2 * ((2 : ℝ) ^ (-(n : ℝ))) ^ (2 * alpha - 1) := by sorry

end FBMStrongSim.RecordBreak.Supplement
