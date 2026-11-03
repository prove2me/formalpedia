-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_marked_void_stationary_of_shared_path_counter
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_void_stationary_of_shared_path_counter
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:41:38.490471+00:00
-- url     : https://prove2.me/theorems/680e2ccc-3f2e-4670-9038-af75a0cb61ff
-- title:
--   Same-source marked void stationarity from a shared measurable jump-path counter
-- statement:
--   For the actual original Lévy jump measure, suppose one globally measurable marked-jump counting functional represents both the future shifted original path and the origin path. Then their exact zero-jump probabilities coincide. The proof invokes the already Proved full original Lévy path stationarity law and transfers a measurable zero-fibre along the same original probability space. No auxiliary process, count intensity or Poisson premise is introduced; the shared path counter is an explicit hypothesis.
-- source:
--   W7-06 path-law portion of original finite-band void stationarity, isolating construction of a shared source-measurable functional from the already proved shifted full-path law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_void_stationary_of_shared_path_counter
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hFuture : ∀ ω : Ω,
      NX ω (Ioc s (s + T) ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω))
    (hOrigin : ∀ ω : Ω,
      NX ω (Ioc 0 T ×ˢ B) =
        F (fun v : ℝ≥0 => X.X v ω)) :
    P {ω : Ω | NX ω (Ioc s (s + T) ×ˢ B) = 0} =
    P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by sorry
