-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_rmt_uniqueness
-- name    : AhlforsComplexAnalysis.rmt_uniqueness
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T12:35:10.113422+00:00
-- url     : https://prove2.me/theorems/4e9f4c95-8b6a-42aa-b645-61e1d10d9c6e
-- title:
--   Uniqueness of the normalised conformal map onto the disk
-- statement:
--   Let $\Omega\subseteq\mathbb C$ be a region (a nonempty open connected set), let $z_0\in\Omega$, and let $\mathbb D=\{w:|w|<1\}$ be the open unit disk. Let $f,g$ be analytic and injective on $\Omega$ with $f(\Omega)=g(\Omega)=\mathbb D$, normalised by $f(z_0)=g(z_0)=0$ and with $f'(z_0)$ and $g'(z_0)$ positive real numbers. Then
--
--   $$f(z)=g(z)\qquad\text{for all }z\in\Omega .$$
--
--   This is the uniqueness half of the Riemann mapping theorem.
--
--   **Formalization Note.** Positivity of the derivative is stated as `0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0`; `IsRegion` is the notion of region from the mission *Ahlfors Complex Analysis I*; `Metric.ball 0 1` is $\mathbb D$.
-- source:
--   L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Ch. 6 section 1.1 (proof of the Riemann mapping theorem, Theorem 1)

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Defs

open AhlforsComplexAnalysis

namespace AhlforsComplexAnalysis

theorem rmt_uniqueness {Ω : Set ℂ} (hΩ : IsRegion Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧ 0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 ∧
      Set.InjOn f Ω ∧ f '' Ω = Metric.ball 0 1)
    (hg : AnalyticOnNhd ℂ g Ω ∧ g z₀ = 0 ∧ 0 < (deriv g z₀).re ∧ (deriv g z₀).im = 0 ∧
      Set.InjOn g Ω ∧ g '' Ω = Metric.ball 0 1) :
    Set.EqOn f g Ω := by sorry

end AhlforsComplexAnalysis
