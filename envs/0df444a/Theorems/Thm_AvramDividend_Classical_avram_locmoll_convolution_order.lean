-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_convolution_order
-- name    : AvramDividend.Classical.avram_locmoll_convolution_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:20:26.176418+00:00
-- url     : https://prove2.me/theorems/677245f6-43f8-41eb-a965-981432a55bca
-- title:
--   Nonnegative one-sided convolution preserves order and vanishes on the negative half-line
-- statement:
--   Nonnegative one-sided convolution preserves order and vanishes on the negative half-line
-- source:
--   Avram localised smoothing: exact decomposition of cc3b5448-3c78-4978-81ca-d6f25ef6998d

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_convolution_order
    (V ρ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hVmono : Monotone V) (hVnonneg : ∀ y, 0 ≤ V y)
    (hVzero : ∀ y < 0, V y = 0)
    (hVsec : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ V v - V u)
    (hρI : Integrable ρ) (hρnorm : (∫ r, ρ r) = 1)
    (hρpos : 0 ≤ᵐ[volume] ρ)
    (hρsupport : ∀ᵐ r ∂volume, ρ r ≠ 0 →
      r ∈ Icc (δ / 3) (2 * (δ / 3)))
    (hI : ∀ y : ℝ, Integrable (fun r => ρ r * V (y - r))) :
    let g : ℝ → ℝ := fun y => ∫ r, ρ r * V (y - r)
    MonotoneOn g (Ici 0) ∧
    (∀ y : ℝ, 0 ≤ g y) ∧
    (∀ y : ℝ, y ≤ 0 → g y = 0) ∧
    (∀ y : ℝ, g y ≤ V y) := by sorry
