-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
-- name    : AvramDividend.Classical.avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:48:31.572818+00:00
-- url     : https://prove2.me/theorems/86562d7b-8188-46f6-8602-23531491875e
-- title:
--   Original canonical dividend discount mesh error is always finite and converges to zero pathwise
-- statement:
--   For the actual original admissible dividend strategy, at any fixed nonnegative stopped physical clock and any nonnegative discount, the precise ENNReal coefficient q/(j+1) times the true dividendMeasure (Ioc 0 t) is never infinite and its toReal vanishes as j tends to infinity. Original rightLimit D interval mass formula ensures finiteness at every clock, without a finite jump-activity assumption. Supplies both strict-pre-ruin stopped cash error finiteness and passage to the real Stieltjes mesh limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    let E : ℕ → ℝ≥0∞ := fun j =>
      ENNReal.ofReal (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))
    (∀ j, E j ≠ ⊤) ∧
    Tendsto (fun j => (E j).toReal) atTop (𝓝 (0 : ℝ)) := by sorry
