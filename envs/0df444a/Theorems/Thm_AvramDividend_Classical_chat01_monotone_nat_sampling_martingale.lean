-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_monotone_nat_sampling_martingale
-- name    : AvramDividend.Classical.chat01_monotone_nat_sampling_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:06:20.002217+00:00
-- url     : https://prove2.me/theorems/63f3c84b-a99f-4717-b340-4ce289e447d1
-- title:
--   Martingale preservation under monotone discrete sampling
-- statement:
--   A martingale indexed by nonnegative real time remains a martingale when sampled along any order-preserving sequence of times indexed by natural numbers, with the corresponding sampled filtration. In particular this supports integer grids and rational time meshes for discrete optional-stopping arguments.
-- source:
--   The Martingale definition and the monotonicity of the sampled filtration.

import Mathlib.Probability.Martingale.Basic
import Mathlib.Data.NNReal.Defs
open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat01_monotone_nat_sampling_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {f : ℝ≥0 → Ω → ℝ}
    (e : ℕ → ℝ≥0) (he : Monotone e) (hf : Martingale f 𝓕 μ) :
    Martingale (fun (n : ℕ) => f (e n))
      ({ seq := fun (n : ℕ) => 𝓕 (e n)
         mono' := by
           intro i j hij
           exact 𝓕.mono (he hij)
         le' := by
           intro n
           exact 𝓕.le (e n) } : Filtration ℕ mΩ) μ := by sorry
