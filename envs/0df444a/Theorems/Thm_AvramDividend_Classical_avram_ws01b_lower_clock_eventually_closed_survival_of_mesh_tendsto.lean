-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_lower_clock_eventually_closed_survival_of_mesh_tendsto
-- name    : AvramDividend.Classical.avram_ws01b_lower_clock_eventually_closed_survival_of_mesh_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:46:48.87447+00:00
-- url     : https://prove2.me/theorems/1eb30c2b-bf75-4a44-8c4b-6a79f15d81af
-- title:
--   Original pre-ruin time approximation eventually preserves full closed survival
-- statement:
--   For the original spectrally negative Lévy path, every sequence of real observation times converging to a time strictly before first strict lower passage eventually has nonnegative reserve on its entire closed observed history. This supplies the exact killed indicator on the upper-first branch of mesh optional stopping.
-- source:
--   Source direct consequence of the Proved original first lower-passage closed survival lemma, continuity of the NNReal-to-ENNReal embedding, and eventual strict inequality in the open order ray.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_lower_clock_strict_preclock_closed_survival

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_lower_clock_eventually_closed_survival_of_mesh_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (ω : Ω) (t : ℝ≥0) (time : ℕ → ℝ≥0)
    (htend : Tendsto time atTop (𝓝 t))
    (hbefore : (t : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω) :
    ∀ᶠ n in atTop, ∀ s : ℝ≥0, s ≤ time n → 0 ≤ x + X.X s ω := by sorry
