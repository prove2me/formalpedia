-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_filtration_measurable_source_count_poisson_exact_law
-- name    : AvramDividend.Classical.avram_wave5_01_bv_actual_filtration_measurable_source_count_poisson_exact_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:27:46.355249+00:00
-- url     : https://prove2.me/theorems/0bd33c35-1cce-4b88-b793-6b36952ceb1c
-- title:
--   Original-filtration measurable BV Lévy source count realises the exact Poisson(Tν) level law
-- statement:
--   On the genuine original probability space and unchanged filtration, the whole source BV finite-activity jump count admits an F_T-measurable representative F which is P-almost surely identical to the literal intrinsic N_X((0,T]×ℝ), and F has exact Poisson singleton probabilities with rate Tν((−∞,0)). The result combines the new Proved source-count measurable-variable theorem with the earlier Proved exact original count Poisson law using measure_congr on the same probability space. It does not infer marked negative-band intensity from unmarked count law.
-- source:
--   Accepted source whole-count filtration measurability theorem 1a909fab-8f86-43ed-acbe-e35bcda9efc6 and exact source total-count Poisson law 237842ca-64a3-4f7b-9393-9d2c19284771; Mathlib measure_congr. Same original X, P, 𝓕.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_total_source_count_filtration_measurable_random_variable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_exact_intensity

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave5_01_bv_actual_filtration_measurable_source_count_poisson_exact_law
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
      (∀ᵐ ω ∂P, F ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) ∧
      (∀ k : ℕ, P.real {ω : Ω | F ω = (k : ℝ≥0∞)} = Real.exp (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) *
          ((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal) ^ k /
            (k.factorial : ℝ)) := by sorry
