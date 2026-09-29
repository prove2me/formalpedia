-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_riemann_mapping_theorem
-- name    : AhlforsComplexAnalysis.riemann_mapping_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T05:15:42.002991+00:00
-- url     : https://prove2.me/theorems/4c8c47ca-218e-4fdf-84c9-d9049c029259
-- title:
--   Riemann mapping theorem
-- statement:
--   Let $\Omega$ be a simply connected region (its complement in the extended plane is connected) which is not the whole plane, and let $z_0\in\Omega$. Then there exists an analytic function $f$ in $\Omega$, normalized by $f(z_0)=0$ and $f'(z_0)>0$, which maps $\Omega$ one-to-one onto the disk $|w|<1$. Moreover this function is unique: any two such functions coincide on $\Omega$.
-- source:
--   L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979 (ISBN 0-07-000657-1), Ch. 6 §1.1, Theorem 1 (p. 230)

import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis

theorem AhlforsComplexAnalysis.riemann_mapping_theorem {Ω : Set ℂ}
    (hΩ : IsSimplyConnectedRegion Ω) (hne : Ω ≠ Set.univ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    (∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧
        0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 ∧
        Set.InjOn f Ω ∧ f '' Ω = Metric.ball 0 1) ∧
    ∀ f g : ℂ → ℂ,
      (AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧ 0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 ∧
        Set.InjOn f Ω ∧ f '' Ω = Metric.ball 0 1) →
      (AnalyticOnNhd ℂ g Ω ∧ g z₀ = 0 ∧ 0 < (deriv g z₀).re ∧ (deriv g z₀).im = 0 ∧
        Set.InjOn g Ω ∧ g '' Ω = Metric.ball 0 1) →
      Set.EqOn f g Ω := by sorry
