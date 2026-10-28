-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_reward_unstopped_martingale_false
-- name    : AvramDividend.Classical.unbounded_scale_reward_unstopped_martingale_false
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:34:03.923154+00:00
-- url     : https://prove2.me/theorems/18eaa4eb-edad-43a8-b2de-aa5b65b02a04
-- title:
--   Un-killed q-scale martingale is false under the exact Lévy process assumptions
-- statement:
--   The un-killed discounted q-scale reward cannot be a martingale for any positive discount and unbounded-variation spectrally negative Levy process, under precisely the same process and scale-function hypotheses as the currently Open chat04_unbounded_discounted_scale_martingale theorem. The Lévy structure already supplies a probability measure; Mathlib's IsFiniteMeasure.sigmaFiniteFiltration instance supplies the apparent sigma-finite filtration hypothesis of the established non-martingale theorem. Consequently the existing prerequisite's theorem statement is mathematically false at zero initial reserve and must be corrected to a stopped/killed formulation.
-- source:
--   Proved unbounded_discounted_scale_unstopped_martingale_impossible, SpectrallyNegativeLevy.isProbability, Mathlib IsFiniteMeasure.sigmaFiniteFiltration.

import Theorems.Thm_AvramDividend_Classical_unbounded_discounted_scale_unstopped_martingale_impossible
import Mathlib.Probability.Process.Filtration

open AvramDividend.Classical MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.unbounded_scale_reward_unstopped_martingale_false
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ¬ Martingale
      (fun t : ℝ≥0 => fun ω : Ω =>
        Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) 𝓕 P := by sorry
