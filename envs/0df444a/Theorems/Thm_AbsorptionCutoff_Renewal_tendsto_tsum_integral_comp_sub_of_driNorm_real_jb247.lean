-- Prove2me | Theorems.Thm_AbsorptionCutoff_Renewal_tendsto_tsum_integral_comp_sub_of_driNorm_real_jb247
-- name    : AbsorptionCutoff.Renewal.tendsto_tsum_integral_comp_sub_of_driNorm_real_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:44:07.431113+00:00
-- url     : https://prove2.me/theorems/79a0458d-be19-4eb3-b9cb-15da3e5dd499
-- title:
--   AbsorptionCutoff.Renewal.tendsto_tsum_integral_comp_sub_of_driNorm_real_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `AbsorptionCutoff.Renewal`, with `open MeasureTheory`, `open scoped Convolution ENNReal NNReal FourierTransform`):
--
--   ```lean
--   theorem tendsto_tsum_integral_comp_sub_of_driNorm_real_jb247 {μ : Measure ℝ}
--       [IsProbabilityMeasure μ]
--       (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
--       {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1)
--       {z : ℝ → ℝ} (hzc : Continuous z) (hz : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) :
--       Filter.Tendsto (fun y : ℝ => ∑' n, ∫ s, z (y - s) ∂(convPow μ n))
--         Filter.atTop (nhds ((∫ x : ℝ, z x) / (∫ x, x ∂μ)))
--   ```
--
--   **Definitions.** The statement is written with `AbsorptionCutoff.Renewal.Nonlattice`, `AbsorptionCutoff.Renewal.convPow`, `AbsorptionCutoff.Renewal.driNorm` and `AbsorptionCutoff.Renewal.expTransform` (definitions bundle `OAIQ247J000` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.NumberTheoryLean.EvenStartOccupation.source_start_occupation_limit_jb247` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Restrict
import Definitions.Def_OAIQ247J000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open MeasureTheory
open scoped Convolution ENNReal NNReal FourierTransform

namespace AbsorptionCutoff

namespace Renewal

theorem tendsto_tsum_integral_comp_sub_of_driNorm_real_jb247 {μ : Measure ℝ}
    [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1)
    {z : ℝ → ℝ} (hzc : Continuous z) (hz : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ s, z (y - s) ∂(convPow μ n))
      Filter.atTop (nhds ((∫ x : ℝ, z x) / (∫ x, x ∂μ))) := by
  sorry

end Renewal

end AbsorptionCutoff
end
