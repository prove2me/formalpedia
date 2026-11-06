-- Prove2me | Theorems.Thm_BianchiIX_hasFDerivAt_moving_intervalIntegral_of_contDiffAt
-- name    : BianchiIX.hasFDerivAt_moving_intervalIntegral_of_contDiffAt
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:07:41.75299+00:00
-- url     : https://prove2.me/theorems/98dd3658-d5c6-4574-9efd-f11124593e4e
-- title:
--   The derivative of a parameter integral with a moving endpoint
-- statement:
--   Let $E$ be a real normed space,
--   $F:E\times\mathbb R\to\mathbb R$, $\tau:E\to\mathbb R$, and $x\in E$.
--   Assume $\tau(x)\geq0$ and define
--   $$M_F(y)=\int_0^{\tau(y)}F(y,t)\,dt,\qquad
--   R(y,s)=\tau(y)F(y,s\tau(y)).$$
--   All interval integrals are oriented integrals.
--   Suppose $\tau$ is $C^1$ at $x$
--   and $F$ is $C^1$ at $(x,t)$ for every $t\in[0,\tau(x)]$. Then $M_F$
--   is Frechet differentiable at $x$, with
--   $$d(M_F)_x=\int_0^1 dR_{(x,s)}\circ\iota_E\,ds,\qquad
--   \iota_E(v)=(v,0).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CompactParametricIntegral.lean#L61-L82

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

theorem BianchiIX.hasFDerivAt_moving_intervalIntegral_of_contDiffAt
    {F : E × ℝ → ℝ} {τ : E → ℝ} {x : E} (hτ : ContDiffAt ℝ 1 τ x) (hpos : 0 ≤ τ x)
    (hF : ∀ t ∈ Icc 0 (τ x), ContDiffAt ℝ 1 F (x, t)) :
    HasFDerivAt (fun y => ∫ t in 0..τ y, F (y, t))
      (∫ t in (0 : ℝ)..1,
        (fderiv ℝ (fun p : E × ℝ => τ p.1 * F (p.1, p.2 * τ p.1)) (x, t)).comp
          (ContinuousLinearMap.inl ℝ E ℝ)) x := by sorry
