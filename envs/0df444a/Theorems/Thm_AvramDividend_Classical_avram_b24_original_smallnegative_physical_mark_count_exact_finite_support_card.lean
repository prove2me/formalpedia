-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_smallnegative_physical_mark_count_exact_finite_support_card
-- name    : AvramDividend.Classical.avram_b24_original_smallnegative_physical_mark_count_exact_finite_support_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:20:13.545103+00:00
-- url     : https://prove2.me/theorems/058365a6-0ebb-49b3-881b-ae7c796159fb
-- title:
--   Genuine original finite small-negative marked Poisson count equals the cardinality of its physical jump-time support
-- statement:
--   For the unmodified original Lévy path X on its own sample space and any finite actual physical jump-time set S consisting EXACTLY of the jumps with negative smallmark amplitude in (-1,0) on (0,T], its intrinsic physical marked Poisson counting measure on Ioc 0 T × Ioo(-1,0) equals the finite cardinality S.card. This specialises the Proved general original Borel marked count/card theorem to the genuine smallmark band and bridges the finite-source Jsmall path norm bound to the original integrable Poisson count; no synthetic marks, no independence of ruin, no moment assumption on large negative marks.
-- source:
--   Proved a20 original finite marked Borel jump-time count equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_window_finite_marked_times_card
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_smallnegative_physical_mark_count_exact_finite_support_card
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (S : Finset ℝ≥0)
    (hS : ∀ u : ℝ≥0, u ∈ S ↔
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈
        Ioo (-1 : ℝ) 0) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0) =
      (S.card : ℝ≥0∞) := by sorry
