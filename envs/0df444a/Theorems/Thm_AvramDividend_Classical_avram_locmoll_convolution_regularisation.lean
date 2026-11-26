-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_convolution_regularisation
-- name    : AvramDividend.Classical.avram_locmoll_convolution_regularisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T19:58:47.453832+00:00
-- url     : https://prove2.me/theorems/cc3b5448-3c78-4978-81ca-d6f25ef6998d
-- title:
--   One-sided convolution of a monotone zero extension: regularity and gradient
-- statement:
--   Smooth a locally integrable monotone candidate by compactly supported convolution. Preserve positivity, monotonicity, the interior unit slope, and the pointwise upper bound from positive translation.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), child of 2e269e44-0ec4-4d09-bac9-26533bf1d8ab

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_convolution_regularisation
    (V ρ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hVmono : Monotone V) (hVnonneg : ∀ y, 0 ≤ V y)
    (hVzero : ∀ y < 0, V y = 0)
    (hVsec : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ V v - V u)
    (hρI : Integrable ρ) (hρnorm : (∫ r, ρ r) = 1)
    (hρpos : 0 ≤ᵐ[volume] ρ)
    (hρsupport : ∀ᵐ r ∂volume, ρ r ≠ 0 →
      r ∈ Icc (δ / 3) (2 * (δ / 3)))
    (hρsmooth : ContDiff ℝ 2 ρ) (hρcompact : HasCompactSupport ρ) :
    let g : ℝ → ℝ := fun y => ∫ r, ρ r * V (y - r)
    (∀ y : ℝ, Integrable (fun r => ρ r * V (y - r))) ∧
    ContDiff ℝ 2 g ∧ MonotoneOn g (Ici 0) ∧
    (∀ y : ℝ, 0 ≤ g y) ∧
    (∀ y : ℝ, y ≤ 0 → g y = 0) ∧
    (∀ y : ℝ, δ ≤ y → 1 ≤ deriv g y) ∧
    (∀ y : ℝ, g y ≤ V y) := by sorry
