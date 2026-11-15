-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a99_original_measurable_physical_marked_jump_measure_dirac_enumeration_20261114
-- name    : AvramDividend.Classical.avram_a99_original_measurable_physical_marked_jump_measure_dirac_enumeration_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:39:28.226199+00:00
-- url     : https://prove2.me/theorems/a348fc62-caa0-440f-9666-7a74262bc83d
-- title:
--   Original Lévy physical marked-jump random measure has an exactly equal countable measurable active Dirac representation
-- statement:
--   For every original spectrally negative Lévy process on its unchanged probability space, construct a measurable countable sequence of actual candidate jump times, active events, and actual jump marks, such that the physical time-mark jump measure is exactly the sum of the corresponding active Dirac measures for every sample path, not merely almost surely. This is a pathwise measurable random-measure representation useful for deriving the finite-activity marked-Poisson Laplace law without postulating an auxiliary Poisson space.
-- source:
--   Proved A96 source measurable jump-time and mark enumeration, and Proved wave5_02a actual physical jump measure equals active enumerated Dirac measures.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a99_original_measurable_physical_marked_jump_measure_dirac_enumeration_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ (T : ℕ → Ω → ℝ≥0) (A : ℕ → Set Ω)
      (Y : ℕ → Ω → ℝ),
      (∀ n, Measurable (T n)) ∧
      (∀ n, MeasurableSet (A n)) ∧
      (∀ n, Measurable (Y n)) ∧
      (∀ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
        Measure.sum (fun n => (A n).indicator
          (fun _ => Measure.dirac (T n ω, Y n ω)) ω)) := by sorry
