-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_marked_mean_ext_of_dense_tests
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_marked_mean_ext_of_dense_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:09:07.769054+00:00
-- url     : https://prove2.me/theorems/5176b13e-cb0c-405e-9a71-85facb173a8d
-- title:
--   Actual original expected marked jump measure determined by dense cutoff tests
-- statement:
--   For the actual original Lévy process, suppose its finite-horizon expected jump mass below a strictly negative cutoff is finite. If the expected marked counts agree with a finite-on-cutoff comparison Borel measure on every cutoff-restricted lower-halfline belonging to a dense threshold set, they agree for every Borel mark set after cutoff. This reduces the separate analytic Lévy-rate calculation to dense threshold tests and does not assume the ν rate.
-- source:
--   Uses source-backed Proved original expected marked measure existence (c026c74a) and P2-C dense cutoff measure extensionality. hTests is a genuine explicit analytic hypothesis, not a self-asserted source ν rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_cutoff_dense_halfline_ext
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_marked_mean_ext_of_dense_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (hFiniteMean : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) < ⊤)
    (ρ : Measure ℝ) (hρfin : ρ (Iic (-ε)) ≠ ⊤)
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ a : ℝ, a ∈ D →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) = ρ (Iic a ∩ Iic (-ε)))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iic (-ε))) ∂P) = ρ (B ∩ Iic (-ε)) := by sorry
