-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_disk_map_is_linear_transformation
-- name    : AhlforsComplexAnalysis.disk_map_is_linear_transformation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T04:56:01.406332+00:00
-- url     : https://prove2.me/theorems/8f745fb8-ebc0-43b5-9a48-2c7d981b7af1
-- title:
--   One-to-one conformal maps of a disk onto a disk are linear transformations
-- statement:
--   Let $D_1=\{|z-a|<r\}$ and $D_2=\{|w-b|<s\}$ be open disks ($r,s>0$), and let $f$ be analytic and one-to-one in $D_1$ with $f(D_1)=D_2$. Then $f$ is a linear (fractional) transformation: there are $\alpha,\beta,\gamma,\delta\in\mathbb C$ with $\alpha\delta-\beta\gamma\neq0$ such that $\gamma z+\delta\neq0$ and
--   $$f(z)=\frac{\alpha z+\beta}{\gamma z+\delta}\qquad\text{for all } z\in D_1.$$
--   This is the disk-onto-disk case of the exercise; the half-plane case is not included.
-- source:
--   L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979 (ISBN 0-07-000657-1), Ch. 4 §3.4, Exercise 5 (p. 136), disk-onto-disk case; used in Ch. 6 §1.1 (p. 230) for the uniqueness in the Riemann mapping theorem

import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis

theorem AhlforsComplexAnalysis.disk_map_is_linear_transformation {a b : ℂ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball a r))
    (hinj : Set.InjOn f (Metric.ball a r)) (honto : f '' Metric.ball a r = Metric.ball b s) :
    ∃ α β γ δ : ℂ, α * δ - β * γ ≠ 0 ∧
      ∀ z ∈ Metric.ball a r, γ * z + δ ≠ 0 ∧ f z = (α * z + β) / (γ * z + δ) := by sorry
