-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_deterministic_simple_mark_fibre_quadratic_energy_from_injective_square_20261122
-- name    : AvramDividend.Classical.avram_oai_deterministic_simple_mark_fibre_quadratic_energy_from_injective_square_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:44:28.073221+00:00
-- url     : https://prove2.me/theorems/e037658e-b628-4233-9513-017300f648d1
-- title:
--   Deterministic exact physical simple mark squared-fibre energy equals squared-mark Lévy integral under square-injective finite range
-- statement:
--   A pure finite simple-function and measure-theoretic identity. If g:ℝ→ₛℝ has its square map injective on its finite range, and g² is integrable over a measurable mark domain S, then Σ over mark fibres y² · (Tν(S∩{g=y})).toReal = T∫_S g²dν. This is a true deterministic intensity-energy identity, with no stochastic assumptions or global finite Lévy activity. It supplies the remaining deterministic premise of the original physical all-activity simple-mark compensated L2 theorem and is suited to nonpositive negative jump-mark quantisers whose ranges lie in [-1,0].

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a20_spatial_Borel_simple_mark_integral_partition
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_deterministic_simple_mark_fibre_quadratic_energy_from_injective_square_20261122
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (g : SimpleFunc ℝ ℝ)
    (hSqInt : IntegrableOn (fun z : ℝ => (g z) ^ 2) S ν)
    (hInj : ∀ x ∈ g.range, ∀ y ∈ g.range, x ^ 2 = y ^ 2 → x = y)
    (T : ℝ≥0) :
    (∑ y ∈ g.range, y ^ 2 *
      ((T : ℝ≥0∞) * ν (S ∩ g ⁻¹' {y})).toReal) =
      (T : ℝ) * (∫ z in S, (g z) ^ 2 ∂ν) := by sorry
