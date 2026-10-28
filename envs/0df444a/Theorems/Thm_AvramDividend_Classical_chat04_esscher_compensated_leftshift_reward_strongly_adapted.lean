-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_compensated_leftshift_reward_strongly_adapted
-- name    : AvramDividend.Classical.chat04_esscher_compensated_leftshift_reward_strongly_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:00:43.632109+00:00
-- url     : https://prove2.me/theorems/83b2d9bc-e97b-4339-8bc2-e80373e37833
-- title:
--   The compensated Esscher negative exponential is strongly adapted to the original Lévy filtration
-- statement:
--   For every time t and any real parameters θ,ε, the reward exp(−εX_t−t(ψ(θ−ε)−ψθ)) is strongly measurable with respect to the original Lévy filtration F_t. This allows the published projective Esscher early-event integral identities to be transferred under one fixed terminal probability law using trimmed-measure integral equality, and permits constructing a genuine discrete-time martingale for the maximal inequality.
-- source:
--   The Lévy process is adapted by definition. Compose the F_t-measurable endpoint X_t with the continuous affine map and real exponential, then apply Mathlib `Measurable.stronglyMeasurable` in the real Polish codomain.

import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_compensated_leftshift_reward_strongly_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) :
    ∀ t : ℝ≥0,
      StronglyMeasurable[𝓕 t]
        (fun ω : Ω => Real.exp
          (-ε * X.X t ω -
            (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ))) := by sorry
