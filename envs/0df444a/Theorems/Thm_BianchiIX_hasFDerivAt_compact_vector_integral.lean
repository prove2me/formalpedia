-- Prove2me | Theorems.Thm_BianchiIX_hasFDerivAt_compact_vector_integral
-- name    : BianchiIX.hasFDerivAt_compact_vector_integral
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:06:03.281467+00:00
-- url     : https://prove2.me/theorems/761bced2-c3c9-41e8-8a79-1bffec77e4f2
-- title:
--   Differentiation of a vector-valued compact parameter integral
-- statement:
--   Let $E,V$ be real normed spaces,
--   $F:E\times\mathbb R\to V$, $x\in E$, and $a\leq b$. Put
--   $$I_F(y)=\int_a^b F(y,t)\,dt,\qquad
--   \partial_EF(y,t)=dF_{(y,t)}\circ\iota_E,\quad \iota_E(v)=(v,0).$$
--   Bochner integrals use the total convention of zero for an incomplete
--   codomain or a nonintegrable integrand.
--   If $F$ is $C^1$ at $(x,t)$
--   for every $t\in[a,b]$, then $I_F$ is Frechet differentiable at $x$, with
--   $$d(I_F)_x=\int_a^b\partial_EF(x,t)\,dt.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CompactVectorIntegral.lean#L13-L52

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
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem BianchiIX.hasFDerivAt_compact_vector_integral {F : E × ℝ → V} {x : E} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 F (x, t)) :
    HasFDerivAt (fun y => ∫ t in a..b, F (y, t))
      (∫ t in a..b, (fderiv ℝ F (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by sorry
