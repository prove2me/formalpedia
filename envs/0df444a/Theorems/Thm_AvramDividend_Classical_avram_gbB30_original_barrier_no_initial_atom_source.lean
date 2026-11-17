-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_barrier_no_initial_atom_source
-- name    : AvramDividend.Classical.avram_gbB30_original_barrier_no_initial_atom_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T13:49:52.75774+00:00
-- url     : https://prove2.me/theorems/54a821be-9f6d-4286-b7cb-51c42f6c11b4
-- title:
--   Any original barrier strategy starting below its cap is admissible and has zero right dividend atoms
-- statement:
--   For every original spectrally negative Levy source and any nonnegative start x below a nonnegative dividend barrier a, the original barrier strategy is admissible and its original right-limit source jump payment inequality holds for any reward w, because the right dividend jump vanishes. This supplies the exact source assumption for all cap levels including 1/8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB30_original_barrier_no_initial_atom_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) (hxa : x ≤ a) :
    IsAdmissibleLe X x (ENNReal.ofReal a) (barrierStrategy X x a) ∧
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) <
        ruinTime X x (barrierStrategy X x a) ω) →
      rightLimit (barrierStrategy X x a) t ω -
        barrierStrategy X x a t ω ≤
      w (riskProcess X x (barrierStrategy X x a) t ω) -
      w (riskProcess X x (barrierStrategy X x a) t ω -
        (rightLimit (barrierStrategy X x a) t ω -
         barrierStrategy X x a t ω)) := by sorry
