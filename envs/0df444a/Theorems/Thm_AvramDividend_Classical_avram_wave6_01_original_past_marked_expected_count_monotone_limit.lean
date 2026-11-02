-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_expected_count_monotone_limit
-- name    : AvramDividend.Classical.avram_wave6_01_original_past_marked_expected_count_monotone_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:03:08.943487+00:00
-- url     : https://prove2.me/theorems/a3756344-9ee6-4190-9980-05a3caea5f92
-- title:
--   Original past-restricted marked jump expectations commute with increasing mark exhaustion
-- statement:
--   For the actual unchanged original Lévy process X, every original past event A∈𝓕_s and every increasing sequence of measurable real-mark sets B_n, the genuine original expected jump count of (s,t]×⋃B_n equals the supremum over n of the past-restricted expected original marked counts on (s,t]×B_n. The source s-finite kernel provides genuine count measurability; Monotone.measure_iUnion gives the fibrewise increasing limit; ENNReal lintegral_iSup gives the expectation limit without finite-activity assumptions. Supports finite-band exhaustion in the eventual ν(B) identification, but assumes neither a compensator nor a Poisson model.
-- source:
--   Canonically Proved actual source intrinsic s-finite kernel; monotone convergence under original P.restrict A, with measure_iUnion on literal source fibres.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_original_past_marked_expected_count_monotone_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hMono : Monotone B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (⋃ n, B n)) ∂P) =
      ⨆ n, (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B n) ∂P) := by sorry
