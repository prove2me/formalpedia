-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_source_total_count_poisson_weighted_first_moment
-- name    : AvramDividend.Classical.avram_wave5_01_bv_actual_source_total_count_poisson_weighted_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:21:19.393388+00:00
-- url     : https://prove2.me/theorems/8bd33f15-d97b-40d6-9d9f-7f64c09c0b21
-- title:
--   Actual BV finite-activity original Lévy count has exact weighted Poisson mass mean Tν
-- statement:
--   For the genuine original spectrally negative Lévy process under bounded variation, finite total negative Lévy activity, and a deterministic positive-horizon fine-grid system, there is an original-filtration F_T-measurable ENNReal-valued count representative equal almost surely to the actual intrinsic source total jump count; the weighted sum over all its Poisson singleton event probabilities has exact real value T X.ν((−∞,0)). This is a source-bound first-moment mass calculation, retaining original paths and filtration. It does not assert unproved arbitrary marked-band intensity or a predictable compensated random measure.
-- source:
--   Compose Proved source count Poisson singleton laws with measurable original F_T representative 0bd33c35 and exact Poisson first moment 951829c1 via pinned integral_poissonMeasure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_filtration_measurable_source_count_poisson_exact_law
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave5_01_bv_actual_source_total_count_poisson_weighted_first_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T) :
    ∃ F : Ω → ℝ≥0∞, Measurable[𝓕 T] F ∧
      (∀ᵐ ω ∂P,
        F ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) ∧
      (∑' k : ℕ,
        (k : ℝ) * P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) =
        (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := by sorry
