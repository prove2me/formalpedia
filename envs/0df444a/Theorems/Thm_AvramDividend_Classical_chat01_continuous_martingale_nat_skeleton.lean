-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_continuous_martingale_nat_skeleton
-- name    : AvramDividend.Classical.chat01_continuous_martingale_nat_skeleton
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:04:09.092213+00:00
-- url     : https://prove2.me/theorems/15eb7fa4-6c38-43c5-82b0-98b8ebe54fad
-- title:
--   Integer-time sampling of a nonnegative-real-time martingale
-- statement:
--   Let f be a martingale indexed by nonnegative real times. Its integer-time samples f(n), relative to the correspondingly sampled filtration F(n), form a discrete-time martingale. This is a reusable bridge for applying discrete-time optional-stopping results to a continuous-time Lévy exponential martingale.
-- source:
--   Martingale definition, strongly adapted sampling and conditional-expectation identities under the order-preserving coercion Nat to NNReal.

import Mathlib.Probability.Martingale.Basic
import Mathlib.Data.NNReal.Defs
open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat01_continuous_martingale_nat_skeleton
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {f : ℝ≥0 → Ω → ℝ}
    (hf : Martingale f 𝓕 μ) :
    Martingale (fun (n : ℕ) => f (n : ℝ≥0))
      ({ seq := fun (n : ℕ) => 𝓕 (n : ℝ≥0)
         mono' := by
           intro i j hij
           exact 𝓕.mono (by exact_mod_cast hij)
         le' := by
           intro i
           exact 𝓕.le (i : ℝ≥0) } : Filtration ℕ mΩ) μ := by sorry
