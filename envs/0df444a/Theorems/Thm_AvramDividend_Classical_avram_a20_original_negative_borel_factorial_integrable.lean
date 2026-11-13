-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_factorial_integrable
-- name    : AvramDividend.Classical.avram_a20_original_negative_borel_factorial_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T10:25:17.068107+00:00
-- url     : https://prove2.me/theorems/51ca3292-96db-4384-926d-b58fbfb4d783
-- title:
--   Original negative-Borel physical factorial jump count is integrable under finite intensity
-- statement:
--   For every measurable negative mark set in the actual original finite-activity spectrally negative Levy process, the real factorial jump count J(J-1) is Bochner integrable. Combine the proved genuine original L2 count for each negative Borel set with the proved exact original count first-moment integrability and the polynomial identity J(J-1)=J squared minus J. This completes the integrability half of the principal JA36 factorial source theorem independently of its still-open exact factorial expectation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_real_count_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_negative_borel_factorial_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let J : Ω → ℝ := fun ω => (N ω).toReal
    Integrable (fun ω => J ω * (J ω - 1)) P := by sorry
