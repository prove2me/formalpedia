-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_convolution_gradient
-- name    : AvramDividend.Classical.avram_locmoll_convolution_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:20:24.348359+00:00
-- url     : https://prove2.me/theorems/cae116b1-82d7-461e-9b34-4161d4617ab6
-- title:
--   Restricted convolution secant implies unit gradient above the strip
-- statement:
--   Restricted convolution secant implies unit gradient above the strip
-- source:
--   Avram localised smoothing: exact decomposition of cc3b5448-3c78-4978-81ca-d6f25ef6998d

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_convolution_gradient
    (V ρ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hVmono : Monotone V) (hVnonneg : ∀ y, 0 ≤ V y)
    (hVzero : ∀ y < 0, V y = 0)
    (hVsec : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ V v - V u)
    (hρI : Integrable ρ) (hρnorm : (∫ r, ρ r) = 1)
    (hρpos : 0 ≤ᵐ[volume] ρ)
    (hρsupport : ∀ᵐ r ∂volume, ρ r ≠ 0 →
      r ∈ Icc (δ / 3) (2 * (δ / 3)))
    (hI : ∀ y : ℝ, Integrable (fun r => ρ r * V (y - r)))
    (hg : ContDiff ℝ 2 (fun y => ∫ r, ρ r * V (y - r))) :
    let g : ℝ → ℝ := fun y => ∫ r, ρ r * V (y - r)
    ∀ y : ℝ, δ ≤ y → 1 ≤ deriv g y := by sorry
