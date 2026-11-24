-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_Supplement_lemma_5_9
-- name    : FBMStrongSim.RecordBreak.Supplement.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:35:25.297811+00:00
-- url     : https://prove2.me/theorems/67be3334-9d4e-4621-aad0-0ce6d30eb242
-- title:
--   Lemma 5.9 — (corrected: zero-norm envelopes) Restricted Hölder composition estimate
-- statement:
--   In the setting of Lemma 5.7, let $y$ be any Young solution and let $y_n$ be the Euler scheme for the same driver and field, allowing different initial values. Set $S=G_1^*+G_1$ and write $H_\alpha(z\mid D_n)$ for the restricted grid seminorm. Then
--   $$H_\alpha(f(y)-f(y_n)\mid D_n)\le(dF_1+d^2F_2S)H_\alpha(y-y_n\mid D_n)+d^2F_2S|y(0)-y_n(0)|.$$
--   Coefficient differences are measured in the maximum entry norm. This statement keeps the printed $G_1$; no dimension correction is propagated into this separate target. The full initial-gap term is retained; this bound controls the nonlinear coefficient difference in the Euler error recursion.
--
--   Differences from the source:
--   - reading: absolute values of vectors, matrices and derivatives → maximum vector norm and maximum absolute derivative entries; reason: the explicit norm convention planned in the brief, making all dimension factors checkable
--   - correction: constants evaluated at the exact derivative norms, including zero norms → F0,F1 are positive uniform entrywise envelopes and F2 is a nonnegative uniform entrywise envelope; reason: the printed ω divides by L=0 for constant fields; for α<1 the printed G1* is also zero when ∇f=0 although a nonzero constant field has a nonconstant solution; see DISPROOF.md; every bounded C² field admits these envelopes
--   - generalization: the same initial value in the displayed Euler system → independent initial values y0,z0 and the displayed initial-gap term; reason: the composition estimate and both regularity bounds are independent of the initial values, so equality of initial values recovers the source
--   - encoding: restricted Hölder supremum over i<j → finite maximum over all ordered pairs, with diagonal quotients zero; reason: absolute increments are symmetric and the grid is finite and nonempty
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 32, Lemma 5.9

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_HolderModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_YoungModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_EulerModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_GridHolderModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_YoungConstants

namespace FBMStrongSim.RecordBreak.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Lemma 5.9 (p.32), retaining the printed constants and the initial-gap term. -/
theorem lemma_5_9 {d h : ℕ} (hd : 0 < d) (hh : 0 < h) {alpha C F0 F1 F2 : ℝ}
    (ha : 1 / 2 < alpha) (ha1 : alpha ≤ 1) (hC : 0 < C)
    {f : Field d h} (hf : CoefficientBounds f F0 F1 F2)
    {x : ℝ → Vec h} (hx : HolderBound alpha C x)
    (y0 z0 : Vec d) {y : ℝ → Vec d} (hy : YoungSolution alpha f x y0 y) (n : ℕ) :
    gridHolder alpha n (fun t => fieldEntries f (y t) - fieldEntries f (euler f x z0 n t)) ≤
      ((d : ℝ) * F1 + (d : ℝ) ^ 2 * F2 *
        (Gstar1 d h alpha C F0 F1 + G1 d h alpha C F0 F1)) *
          gridHolder alpha n (fun t => y t - euler f x z0 n t) +
      (d : ℝ) ^ 2 * F2 * (Gstar1 d h alpha C F0 F1 + G1 d h alpha C F0 F1) *
        ‖y 0 - euler f x z0 n 0‖ := by sorry

end FBMStrongSim.RecordBreak.Supplement
