-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_scale_reward_measurable
-- name    : AvramDividend.Classical.chat03_grid_stopped_scale_reward_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-22T05:46:16.976813+00:00
-- url     : https://prove2.me/theorems/2c11b619-825a-4742-8096-2c497ddbf63f
-- title:
--   Discounted scale reward at a bounded grid first exit is measurable
-- statement:
--   For a spectrally negative Lévy process with its canonical Borel q-scale function and a true bounded two-sided discrete first-passage time, the discounted stopped scale reward is measurable. The proof uses accepted measurability of the sampled reserve and sampled clock, Borel measurability of W, and closure of measurable real functions under arithmetic and exponentiation. It requires no harmonicity or optional stopping.
-- source:
--   Compose accepted chat03_grid_stopped_reserve_time_measurable and chat03_scale_function_borel_measurable with standard Mathlib measurable exponential, negation, product, sum and composition lemmas.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_grid_stopped_scale_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    Measurable (fun ω =>
      Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) := by
  sorry
