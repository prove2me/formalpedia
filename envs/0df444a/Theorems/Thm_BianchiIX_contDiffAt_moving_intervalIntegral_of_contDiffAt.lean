-- Prove2me | Theorems.Thm_BianchiIX_contDiffAt_moving_intervalIntegral_of_contDiffAt
-- name    : BianchiIX.contDiffAt_moving_intervalIntegral_of_contDiffAt
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:09:38.987206+00:00
-- url     : https://prove2.me/theorems/64f5175a-4dcb-440e-9b2a-8c50bacd6d30
-- title:
--   Continuous differentiability for a moving interval integral
-- statement:
--   Let $E$ be a real normed space,
--   $F:E\times\mathbb R\to\mathbb R$, $\tau:E\to\mathbb R$, and $x\in E$.
--   Assume $\tau(x)\geq0$ and define
--   $$M_F(y)=\int_0^{\tau(y)}F(y,t)\,dt,\qquad
--   R(y,s)=\tau(y)F(y,s\tau(y)).$$
--   All interval integrals are oriented integrals.
--   If $\tau$ is $C^1$ at $x$ and
--   $F$ is $C^1$ at every $(x,t)$ with $t\in[0,\tau(x)]$, then $M_F$ is
--   $C^1$ at $x$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CompactIntegralRegularity.lean#L50-L66

import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BianchiIX.contDiffAt_moving_intervalIntegral_of_contDiffAt
    {F : E × ℝ → ℝ} {τ : E → ℝ} {x : E} (hτ : ContDiffAt ℝ 1 τ x) (hpos : 0 ≤ τ x)
    (hF : ∀ t ∈ Icc 0 (τ x), ContDiffAt ℝ 1 F (x, t)) :
    ContDiffAt ℝ 1 (fun y => ∫ t in 0..τ y, F (y, t)) x := by sorry
