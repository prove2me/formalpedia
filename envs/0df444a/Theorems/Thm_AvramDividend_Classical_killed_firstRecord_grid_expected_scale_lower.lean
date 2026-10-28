-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_expected_scale_lower
-- name    : AvramDividend.Classical.killed_firstRecord_grid_expected_scale_lower
-- status  : Open
-- author  : @WillR
-- created : 2026-10-25T15:13:01.858673+00:00
-- url     : https://prove2.me/theorems/77dc4109-c325-41aa-a80c-9cd7723cdf3a
-- title:
--   Discounted surviving first-record payments dominate the left scale-ratio geometric sequence
-- statement:
--   For a standing spectrally negative Lévy process and its positive q-scale function W, let ε be a record-height increment smaller than the ruin barrier a, and suppose 0 ≤ W(a−ε) < W(a). For every n, the expected discounted payment of size ε at the (n+1)st strict upward record crossing, killed if ruin precedes that crossing, is at least ε times the (n+1)st power of W(a−ε)/W(a). This is the stochastic first-passage and strong-Markov renewal estimate missing from the independently Proved pathwise record-grid budget.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 and the two-sided q-scale exit identity; the missing input is the stopped first-passage Markov regeneration estimate, with the exact indicator and discounting under P.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat08_record_grid_stopped_weights_aemeasurable

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_firstRecord_grid_expected_scale_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a) :
    ∀ n : ℕ,
      ENNReal.ofReal (ε * (W (a - ε) / W a) ^ (n + 1)) ≤
        (∫⁻ ω,
          if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (ε * Real.exp
              (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
          else 0 ∂P) := by sorry
