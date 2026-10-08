-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_rmt_exists_extremal
-- name    : AhlforsComplexAnalysis.rmt_exists_extremal
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T12:34:56.129156+00:00
-- url     : https://prove2.me/theorems/11dd55e4-7c31-4b9b-a786-e5dadb7cf5fc
-- title:
--   The extremal problem for the Riemann mapping theorem
-- statement:
--   Let $\Omega\subsetneq\mathbb C$ be a region (nonempty, open, connected) with $\Omega\ne\mathbb C$, let $z_0\in\Omega$, and assume that every nowhere vanishing analytic function on $\Omega$ has an analytic square root. Let $\mathcal F$ be the family of injective analytic functions $h:\Omega\to\mathbb D$ into the open unit disk with $h(z_0)=0$. Then $\mathcal F$ contains an element $f$ with $f'(z_0)\ne 0$ that maximises $|h'(z_0)|$ over $\mathcal F$:
--
--   $$|h'(z_0)|\le |f'(z_0)|\qquad\text{for all }h\in\mathcal F .$$
--
--   This is the extremal step of Ahlfors' proof of the Riemann mapping theorem. The hypothesis on square roots is what holds on a simply connected region.
--
--   **Formalization Note.** `IsRegion` is the notion of region (nonempty, open, connected) from the mission *Ahlfors Complex Analysis I*; `Metric.ball 0 1` is the open unit disk $\mathbb D$.
-- source:
--   L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Ch. 6 section 1.1 (proof of the Riemann mapping theorem, Theorem 1)

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Defs

open AhlforsComplexAnalysis

namespace AhlforsComplexAnalysis

theorem rmt_exists_extremal {Ω : Set ℂ} (hΩ : IsRegion Ω) (hne : Ω ≠ Set.univ)
    (hroot : ∀ u : ℂ → ℂ, AnalyticOnNhd ℂ u Ω → (∀ z ∈ Ω, u z ≠ 0) →
      ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r Ω ∧ ∀ z ∈ Ω, r z ^ 2 = u z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f Ω ∧ (∀ z ∈ Ω, ‖f z‖ < 1) ∧ f z₀ = 0 ∧ Set.InjOn f Ω ∧
      deriv f z₀ ≠ 0 ∧
      ∀ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω → (∀ z ∈ Ω, ‖h z‖ < 1) → h z₀ = 0 → Set.InjOn h Ω →
        ‖deriv h z₀‖ ≤ ‖deriv f z₀‖ := by sorry

end AhlforsComplexAnalysis
