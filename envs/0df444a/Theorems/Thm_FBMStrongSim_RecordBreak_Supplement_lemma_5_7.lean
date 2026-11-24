-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_Supplement_lemma_5_7
-- name    : FBMStrongSim.RecordBreak.Supplement.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:32:59.687554+00:00
-- url     : https://prove2.me/theorems/5a811222-2967-453f-b07a-736708001b01
-- title:
--   Lemma 5.7 — (corrected: zero-norm envelopes) Young solution existence and estimates
-- statement:
--   Let $d,h\ge1$, $1/2<\alpha\le1$, and let $x:[0,1]\to\mathbb R^h$ be $\alpha$-Hölder with constant $C>0$. Suppose $f$ is bounded $C^2$ with entrywise envelopes $F_0,F_1>0$ and $F_2\ge0$. For each initial value $y_0$, a Young solution exists. Every Young solution starting at $y_0$ satisfies, for $0\le s<t\le1$,
--   $$|y(t)-y(s)|\le G_1^*|t-s|^\alpha,\qquad |y(t)-y(s)-f(y(s))(x(t)-x(s))|\le G_2^*|t-s|^{2\alpha}.$$
--   The constants $G_1^*,G_2^*$ are computed in YoungConstants from $d,h,\alpha,C,F_0,F_1$. Existence is a separate conclusion and Hölder regularity is not assumed in the definition of solution.
--
--   Differences from the source:
--   - reading: absolute values of vectors, matrices and derivatives → maximum vector norm and maximum absolute derivative entries; reason: the explicit norm convention planned in the brief, making all dimension factors checkable
--   - correction: constants evaluated at the exact derivative norms, including zero norms → F0,F1 are positive uniform entrywise envelopes and F2 is a nonnegative uniform entrywise envelope; reason: the printed ω divides by L=0 for constant fields; for α<1 the printed G1* is also zero when ∇f=0 although a nonzero constant field has a nonconstant solution; see DISPROOF.md; every bounded C² field admits these envelopes
--   - encoding: a solution in Definitions 5.1–5.2 → a continuous path with finite compatible q-variation satisfying the common left Riemann-sum limit; reason: this retains the source solution class without assuming the Hölder estimate being proved
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 31, Lemma 5.7

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_HolderModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_YoungModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_EulerModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_GridHolderModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_YoungConstants

namespace FBMStrongSim.RecordBreak.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Lemma 5.7 (p.31): existence, and estimates for every Young solution. -/
theorem lemma_5_7 {d h : ℕ} (hd : 0 < d) (hh : 0 < h) {alpha C F0 F1 F2 : ℝ}
    (ha : 1 / 2 < alpha) (ha1 : alpha ≤ 1) (hC : 0 < C)
    {f : Field d h} (hf : CoefficientBounds f F0 F1 F2)
    {x : ℝ → Vec h} (hx : HolderBound alpha C x)
    (y0 : Vec d) :
    (∃ y : ℝ → Vec d, YoungSolution alpha f x y0 y) ∧
    (∀ y : ℝ → Vec d, YoungSolution alpha f x y0 y →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, s < t →
        ‖y t - y s‖ ≤ Gstar1 d h alpha C F0 F1 * (t - s) ^ alpha ∧
        ‖y t - y s - f (y s) (x t - x s)‖ ≤
          Gstar2 d h alpha C F0 F1 * (t - s) ^ (2 * alpha)) := by sorry

end FBMStrongSim.RecordBreak.Supplement
