-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a285_first_order_discount_expected_energy_budget
-- name    : AvramDividend.Classical.avram_ga_a285_first_order_discount_expected_energy_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:32:09.410439+00:00
-- url     : https://prove2.me/theorems/fa876025-5b46-4aa5-88ef-33f326163dd4
-- title:
--   Expected Gaussian discounted first-order residual uniformly bounded by arbitrary raw-energy budget plus eventually negligible mesh correction
-- statement:
--   If an integrable true finite-grid first-order discounted source S_m is dominated pathwise by η times an integrable raw quadratic energy E_m plus a deterministic mesh correction a_m tending to zero, and expected E_m is uniformly bounded by K, then for every tolerance ζ>0 the expected source is eventually at most ηK+ζ. This is the exact integrated route from masked Young a283, original Gaussian raw expected energy a240 and physical discount correction a284 to the original small-cell expected tolerance a264.
-- source:
--   Original Gaussian smallcell discount first-order Young expected energy route a283/a284/a240

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a285_first_order_discount_expected_energy_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S E : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (η K : ℝ) (hη : 0 ≤ η)
    (hSI : ∀ m, Integrable (S m) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hExpected : ∀ m, (∫ ω, E m ω ∂P) ≤ K)
    (hPt : ∀ m ω, S m ω ≤ η*E m ω+a m)
    (hRate : Tendsto a atTop (𝓝 (0:ℝ))) :
    ∀ ζ, 0 < ζ → ∃ k : ℕ, ∀ m, k ≤ m →
      (∫ ω, S m ω ∂P) ≤ η*K+ζ := by sorry
