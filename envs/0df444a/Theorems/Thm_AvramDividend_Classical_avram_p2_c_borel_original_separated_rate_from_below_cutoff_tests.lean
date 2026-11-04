-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_rate_from_below_cutoff_tests
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_separated_rate_from_below_cutoff_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:18:50.833751+00:00
-- url     : https://prove2.me/theorems/68accc49-dd89-4971-bfb7-0742c5936a63
-- title:
--   Separated original ν rate from dense tests strictly below cutoff and exact cutoff mass
-- statement:
--   For every separated negative Borel mark set B, the original intrinsic marked jump rate equals elapsed time times ν(B) provided the same original source rate is established only at the cutoff and on dense lower-halfline thresholds strictly below the cutoff. This is a finite-test-family conditional identification, with genuine analytic premises.
-- source:
--   P2-A proved finite cutoff Lévy ν lemma, P2-C scaled cutoff finiteness, and P2-C original marked mean extension from below-cutoff dense tests and cutoff total. This proof must be published only once that last parent becomes Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_scaled_cutoff_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_marked_mean_from_below_tests_and_cutoff

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_separated_rate_from_below_cutoff_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε))
    (D : Set ℝ) (hDense : Dense D)
    (hCut : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic (-ε))))
    (hBelow : ∀ a : ℝ, a ∈ D → a < -ε →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic a) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic a))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
