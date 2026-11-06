-- Prove2me | Theorems.Thm_BianchiIX_contDiffAt_moving_intervalIntegral_two
-- name    : BianchiIX.contDiffAt_moving_intervalIntegral_two
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:10:47.725328+00:00
-- url     : https://prove2.me/theorems/a294dff2-2a5c-4ab1-b20c-2c69e1ce0018
-- title:
--   Twice continuous differentiability of a moving interval integral
-- statement:
--   Let $E$ be a real normed space,
--   $F:E\times\mathbb R\to\mathbb R$, $\tau:E\to\mathbb R$, and $x\in E$.
--   Assume $\tau(x)\geq0$ and define
--   $$M_F(y)=\int_0^{\tau(y)}F(y,t)\,dt,\qquad
--   R(y,s)=\tau(y)F(y,s\tau(y)).$$
--   All interval integrals are oriented integrals.
--   If $\tau$ is $C^2$ at $x$ and
--   $F$ is $C^2$ at every $(x,t)$ with $t\in[0,\tau(x)]$, then $M_F$ is
--   $C^2$ at $x$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CompactIntegralSecondRegularity.lean#L30-L46

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

theorem BianchiIX.contDiffAt_moving_intervalIntegral_two
    {F : E × ℝ → ℝ} {τ : E → ℝ} {x : E} (hτ : ContDiffAt ℝ 2 τ x) (hpos : 0 ≤ τ x)
    (hF : ∀ t ∈ Icc 0 (τ x), ContDiffAt ℝ 2 F (x, t)) :
    ContDiffAt ℝ 2 (fun y => ∫ t in 0..τ y, F (y, t)) x := by sorry
