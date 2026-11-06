-- Prove2me | Theorems.Thm_BianchiIX_exists_bounds_of_vanishing_axis
-- name    : BianchiIX.exists_bounds_of_vanishing_axis
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:48:34.837749+00:00
-- url     : https://prove2.me/theorems/ef575d14-882a-4697-ba5c-5d80489d0e4c
-- title:
--   A vanishing axis and zero first derivative give separate axial and transverse bounds
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $V$
--   a real normed space, $R\geq0$, and $F:\mathbb R\times E\to V$.
--   Assume $F$ is $C^3$ at every $x$ with $\|x\|\leq R$,
--   $F(n,0)=0$ for every real $n$, and $dF_0=0$. There exists $C\geq1$
--   such that throughout that closed ball,
--   $$\|F(x)\|\leq C\|x\|\|x_2\|,\qquad \|dF_x\|\leq C\|x\|,
--   \qquad \|dF_x(1,0)\|\leq C\|x_2\|.$$
--   The product norm is the maximum norm and $x_2$ denotes the $E$ component.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/VanishingAxis.lean#L14-L72

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_bounds_of_vanishing_axis
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ℝ × E → V} {R : ℝ} (hR : 0 ≤ R)
    (hreg : ∀ x : ℝ × E, ‖x‖ ≤ R → ContDiffAt ℝ 3 F x)
    (haxis : ∀ n : ℝ, F (n, 0) = 0) (hzero : fderiv ℝ F 0 = 0) :
    ∃ C ≥ (1 : ℝ), ∀ x : ℝ × E, ‖x‖ ≤ R →
      ‖F x‖ ≤ C * ‖x‖ * ‖x.2‖ ∧
      ‖fderiv ℝ F x‖ ≤ C * ‖x‖ ∧
      ‖fderiv ℝ F x (1, 0)‖ ≤ C * ‖x.2‖ := by sorry
