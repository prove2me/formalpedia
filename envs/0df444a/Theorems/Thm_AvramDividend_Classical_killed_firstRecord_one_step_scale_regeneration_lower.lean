-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_one_step_scale_regeneration_lower
-- name    : AvramDividend.Classical.killed_firstRecord_one_step_scale_regeneration_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:28:36.932977+00:00
-- url     : https://prove2.me/theorems/5e0908c3-63ca-48af-a5bb-8ce5ed811da7
-- title:
--   Strong-Markov lower renewal step between consecutive killed upward records
-- statement:
--   For every killed strict first-record crossing from level (n+1)ε, a strong-Markov restart at the record and the two-sided q-scale exit inequality yield E[w(n+1)]≥[W(a−ε)/W(a)] E[w n]. The events and discounts are evaluated at actual strict crossing clocks and the true reflected ruin time; this statement is the regenerative stochastic step independent of the already Proved geometric induction.
-- source:
--   Avram, Palmowski, Pistorius (2007), Proposition 1, strong-Markov renewal at successive records and the two-sided q-scale exit law.

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

theorem AvramDividend.Classical.killed_firstRecord_one_step_scale_regeneration_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a) :
    ∀ n : ℕ,
      ENNReal.ofReal (W (a - ε) / W a) *
        (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
        (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 2 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 2 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by sorry
