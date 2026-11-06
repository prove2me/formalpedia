-- Prove2me | Theorems.Thm_BianchiIX_contDiffAt_intervalIntegral_two
-- name    : BianchiIX.contDiffAt_intervalIntegral_two
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:09:55.326989+00:00
-- url     : https://prove2.me/theorems/6d412874-66c1-49f1-b0cd-f13d0124e428
-- title:
--   Twice continuous differentiability under integration
-- statement:
--   Let $E$ be a real normed space,
--   $F:E\times\mathbb R\to\mathbb R$, $x\in E$, and $a\leq b$.
--   Write $\partial_EF(y,t)=dF_{(y,t)}\circ\iota_E$, where
--   $\iota_E(v)=(v,0)$, and set
--   $$I_F(y)=\int_a^b F(y,t)\,dt.$$
--   If $F$ is $C^2$ at $(x,t)$
--   for every $t\in[a,b]$, then $I_F$ is $C^2$ at $x$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CompactIntegralSecondRegularity.lean#L12-L28

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

theorem BianchiIX.contDiffAt_intervalIntegral_two {F : E × ℝ → ℝ} {x : E} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ t ∈ Icc a b, ContDiffAt ℝ 2 F (x, t)) :
    ContDiffAt ℝ 2 (fun y => ∫ t in a..b, F (y, t)) x := by sorry
