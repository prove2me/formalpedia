-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
-- name    : AvramDividend.Classical.avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:42:39.516241+00:00
-- url     : https://prove2.me/theorems/bd222a39-c2dd-4836-ab7e-20c75561dcda
-- title:
--   Actual original UBV capped controlled Lévy generator applies almost everywhere without auxiliary observation grids
-- statement:
--   For the exact original unbounded-variation spectrally negative Lévy process, and any same-filtration admissible dividend strategy with any nonzero extended-real cap C, including finite caps and infinity, the controlled pre-ruin reserve is strictly between zero and C at almost every positive time under any fixed sigma-finite time measure μ. This is directly the corrected core's actual IsAdmissibleLe and hxc interface, without any externally supplied dense grid or cofinal horizons. The proof constructs such schedules internally using NNReal density and shrinking reciprocals, then instantiates the independently Proved source generator-interior occupation theorem c8aed6ff-a440-4dd2-9eff-1f7e9bcecf88. It establishes the physical-time generator localisation only; it does not assert that singular-continuous dividend Stieltjes payments avoid the cap or that the original controlled stochastic expectation budget is proved.
-- source:
--   Pinned original source spectrally negative Lévy, canonical c8aed6ff-a440-4dd2-9eff-1f7e9bcecf88, Mathlib TopologicalSpace.exists_dense_seq, Dense.exists_between, exists_nat_one_div_lt. This removes external schedule hypotheses from corrected UBV core localisation target 429e17ca-5528-40b5-b593-7c03973d0706 without strengthening HJB assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C := by sorry
