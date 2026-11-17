-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_negative_Borel_grid_occupied_indicator_iid_20261116
-- name    : AvramDividend.Classical.avram_a26_original_negative_Borel_grid_occupied_indicator_iid_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:17:47.193792+00:00
-- url     : https://prove2.me/theorems/5675ea4f-1aea-4bb0-a419-d8bf03013665
-- title:
--   The original physical negative-Borel occupied grid indicators are independent and identically distributed
-- statement:
--   For the actual finite-negative-activity marked jumps of the original spectrally negative Lévy process, the indicator that each consecutive equal-width physical time cell contains a B-marked jump is measurable. All indicators on one finite grid form a jointly independent family on the unchanged original Omega and P, and have identical Bernoulli probabilities equal to one minus the actual physical void probability of the first cell. Derive joint independence by induction using the proved original future shifted marked-count independence from any past observable 0832c67e and filtration measurability; derive identical probabilities from original stationary increments 37abf3aa. No independent companion process is constructed.
-- source:
--   Original source future-past marked count independence 0832c67e, stationary physical count law 37abf3aa, marked-count measurability b25029d5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a26_original_negative_Borel_grid_occupied_indicator_iid_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (n : ℕ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℝ≥0 := T / (n : ℝ≥0)
    let Y : Fin n → Ω → ℕ := fun i ω =>
      if NX ω (Ioc ((i.val : ℝ≥0) * δ)
        (((i.val + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B) = 0
      then 0 else 1
    (∀ i, Measurable (Y i)) ∧
      iIndepFun Y P ∧
      ∀ i : Fin n, P {ω : Ω | Y i ω = 1} =
        P {ω : Ω | NX ω (Ioc 0 δ ×ˢ B) ≠ 0} := by sorry
