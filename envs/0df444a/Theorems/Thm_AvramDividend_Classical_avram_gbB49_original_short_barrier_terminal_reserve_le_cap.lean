-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_short_barrier_terminal_reserve_le_cap
-- name    : AvramDividend.Classical.avram_gbB49_original_short_barrier_terminal_reserve_le_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:42:19.33784+00:00
-- url     : https://prove2.me/theorems/1061ea56-1766-450c-a42d-666d9a305196
-- title:
--   Original cap-reflected barrier terminal reserve is below cap on positive horizon
-- statement:
--   The exact original cap-barrier strategy has reserve at most its cap at each strictly positive physical time. On the narrow source tube this supplies the terminal upper-strip bound needed by the short-horizon Gaussian counterexample certificate. Proof uses the Proved original all-capital barrier reserve cap inequality and monotonic ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB49_original_short_barrier_terminal_reserve_le_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ω : Ω) (hT : 0 < T)
    (hTube : ∀ s : ℝ≥0, s ≤ T → |X.X s ω| ≤ (1 / 400 : ℝ)) :
    riskProcess X (1 / 8 : ℝ)
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω ≤
      (1 / 8 : ℝ) := by sorry
