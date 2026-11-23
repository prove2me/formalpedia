-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_mark_vector_adjacent_time_independence
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_original_mark_vector_adjacent_time_independence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:15:01.020741+00:00
-- url     : https://prove2.me/theorems/b1190ab0-171b-47da-b4c8-6980a39420f7
-- title:
--   Original spectrally negative Lévy finite marked-count vectors in adjacent time windows are jointly independent
-- statement:
--   For any finite family of Borel mark sets and the unchanged original spectrally negative Lévy probability space, the whole vector of physical marked jump counts observed on (0,s] is independent of the whole vector of marked jump counts observed on (s,s+T]. Derive the past-vector filtration measurability pointwise from Proved original a28 Borel count adaptedness; then apply the original finite-vector future functional independence theorem. Spatial independence between coordinates within the same interval is neither assumed nor concluded.
-- source:
--   Original Proved a28 physical Borel cell count filtration measurability 60ce8fc6 and A77 finite-vector original future-independence bridge da95ae77.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_original_mark_vector_adjacent_time_independence
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ)
    (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    IndepFun
      (fun ω : Ω => fun i : Fin n =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ B i))
      (fun ω : Ω => fun i : Fin n =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s (s + T) ×ˢ B i)) P := by sorry
