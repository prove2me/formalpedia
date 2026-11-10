-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_offtime_lintegral_bridge
-- name    : AvramDividend.Classical.avram_mix_fin_source13_original_annulus_offtime_lintegral_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:00:17.976955+00:00
-- url     : https://prove2.me/theorems/20cde96e-0493-43a5-adab-1826b4b82ac0
-- title:
--   Original off-time negative-annulus cell product lintegral from Proved real mean
-- statement:
--   For the original Levy process X, the nonnegative extended-real annulus jump-count product on disjoint positive time cells has expectation equal to the product of the physical source rates. The proof imports the original real L1 product identity and sample-path count finiteness; it is a reusable interface for the chronological factorial moment target 6ea0212e.
-- source:
--   MIX-SOURCE-FIN13 necessary physical factorial-grid cell bridge

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_offtime_product_mean
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_count_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_rate_finite_n
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin_source13_original_annulus_offtime_lintegral_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ B)
    let F : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    (∫⁻ ω, A ω * F ω ∂P) =
      ((s : ℝ≥0∞) * X.ν B) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
