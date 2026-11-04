-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_marked_mean_from_below_tests_and_cutoff
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_marked_mean_from_below_tests_and_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:55:21.89084+00:00
-- url     : https://prove2.me/theorems/66c93dd8-5906-4e68-b2e3-302e41fd41be
-- title:
--   Original expected negative-cutoff Borel measure from only below-cutoff dense tests and cutoff total
-- statement:
--   For original Lévy literal marked counts on a genuine probability space, equality to a finite comparison measure on the negative cutoff and on lower half-lines from a dense set strictly below the cutoff suffices to give equality for every Borel mark subset of the cutoff. Above-cutoff analytic tests and a separate original finite-mean hypothesis are unnecessary.
-- source:
--   Apply already Proved original_marked_mean_ext_of_dense_tests_no_finite_mean after deriving its dense truncated threshold identities by splitting a<−ε and a≥−ε, exactly as in the Proved abstract cutoff_dense_below_ext helper. No ν rate is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_marked_mean_ext_of_dense_tests_no_finite_mean

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_marked_mean_from_below_tests_and_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (ρ : Measure ℝ) (hρfin : ρ (Iic (-ε)) ≠ ⊤)
    (D : Set ℝ) (hDense : Dense D)
    (hCut : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) = ρ (Iic (-ε)))
    (hBelow : ∀ a : ℝ, a ∈ D → a < -ε →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic a) ∂P) = ρ (Iic a))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iic (-ε))) ∂P) = ρ (B ∩ Iic (-ε)) := by sorry
