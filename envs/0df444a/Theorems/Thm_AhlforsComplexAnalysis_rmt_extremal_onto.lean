-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_rmt_extremal_onto
-- name    : AhlforsComplexAnalysis.rmt_extremal_onto
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T12:35:04.064389+00:00
-- url     : https://prove2.me/theorems/20fdeac5-0f44-409b-9ca0-7d9f8ffa1b00
-- title:
--   An extremal function maps onto the unit disk
-- statement:
--   Let $\Omega$ be a region on which every nowhere vanishing analytic function has an analytic square root, and let $z_0\in\Omega$. Let $f:\Omega\to\mathbb D$ be analytic and injective with $f(z_0)=0$ and $f'(z_0)\ne0$, and suppose $|h'(z_0)|\le|f'(z_0)|$ for every injective analytic $h:\Omega\to\mathbb D$ with $h(z_0)=0$. Then $f$ maps $\Omega$ onto the unit disk:
--
--   $$f(\Omega)=\mathbb D .$$
--
--   This is the surjectivity step in Ahlfors' proof of the Riemann mapping theorem: a function that maximises the derivative at $z_0$ among injective maps into the disk cannot omit any point of the disk.
--
--   **Formalization Note.** `IsRegion` is the notion of region from the mission *Ahlfors Complex Analysis I*; `Metric.ball 0 1` is the open unit disk $\mathbb D$.
-- source:
--   L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Ch. 6 section 1.1 (proof of the Riemann mapping theorem, Theorem 1)

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Defs

open AhlforsComplexAnalysis

namespace AhlforsComplexAnalysis

theorem rmt_extremal_onto {Ω : Set ℂ} (hΩ : IsRegion Ω)
    (hroot : ∀ u : ℂ → ℂ, AnalyticOnNhd ℂ u Ω → (∀ z ∈ Ω, u z ≠ 0) →
      ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r Ω ∧ ∀ z ∈ Ω, r z ^ 2 = u z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) (hfmap : ∀ z ∈ Ω, ‖f z‖ < 1)
    (hf0 : f z₀ = 0) (hfinj : Set.InjOn f Ω) (hfd : deriv f z₀ ≠ 0)
    (hmax : ∀ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω → (∀ z ∈ Ω, ‖h z‖ < 1) → h z₀ = 0 → Set.InjOn h Ω →
      ‖deriv h z₀‖ ≤ ‖deriv f z₀‖) :
    f '' Ω = Metric.ball 0 1 := by sorry

end AhlforsComplexAnalysis
