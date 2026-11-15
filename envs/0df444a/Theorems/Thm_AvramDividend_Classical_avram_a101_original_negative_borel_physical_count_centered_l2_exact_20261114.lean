-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a101_original_negative_borel_physical_count_centered_l2_exact_20261114
-- name    : AvramDividend.Classical.avram_a101_original_negative_borel_physical_count_centered_l2_exact_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:42:09.836008+00:00
-- url     : https://prove2.me/theorems/8c35a84f-1e32-4e56-a542-aa38135166de
-- title:
--   Original physical negative Borel jump count: centred square integrable and exact rate variance
-- statement:
--   For the actual physical negative Borel jump-count random variable on the original spectrally negative Levy probability space with finite total negative mark mass, the squared count minus its exact mean is integrable and its variance equals the Poisson rate T ν(B). This uses only original-source first and second moment identities and requires no imported full Poisson distribution or zero Gaussian volatility assumption.
-- source:
--   Already Proved JA35 original negative Borel count exact first moment and A20 original negative Borel exact raw second moment. Expand square algebraically and integrate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a101_original_negative_borel_physical_count_centered_l2_exact_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
      (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r := by sorry
