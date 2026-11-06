-- Prove2me | Theorems.Thm_BianchiIX_hasFDerivAt_intervalIntegral_of_contDiffAt
-- name    : BianchiIX.hasFDerivAt_intervalIntegral_of_contDiffAt
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:05:59.873317+00:00
-- url     : https://prove2.me/theorems/9817ef1f-2652-4fec-b80a-c87579c44a1c
-- title:
--   Differentiation of a parameter integral from local compact regularity
-- statement:
--   Let $E$ be a real normed space,
--   $F:E\times\mathbb R\to\mathbb R$, $x\in E$, and $a\leq b$.
--   Write $\partial_EF(y,t)=dF_{(y,t)}\circ\iota_E$, where
--   $\iota_E(v)=(v,0)$, and set
--   $$I_F(y)=\int_a^b F(y,t)\,dt.$$
--   If $F$ is $C^1$ at $(x,t)$
--   for every $t\in[a,b]$, then $I_F$ is Frechet differentiable at $x$ and
--   $$d(I_F)_x=\int_a^b\partial_EF(x,t)\,dt.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CompactParametricIntegral.lean#L14-L53

import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BianchiIX.hasFDerivAt_intervalIntegral_of_contDiffAt {F : E × ℝ → ℝ} {x : E} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 F (x, t)) :
    HasFDerivAt (fun y => ∫ t in a..b, F (y, t))
      (∫ t in a..b, (fderiv ℝ F (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by sorry
