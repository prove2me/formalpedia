-- Prove2me | Theorems.Thm_AvramDividend_Classical_martingale_sample_nat
-- name    : AvramDividend.Classical.martingale_sample_nat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:37:11.620271+00:00
-- url     : https://prove2.me/theorems/8b7af7ab-6ab9-4f31-a72c-81c25ce0eac6
-- title:
--   A nonnegative-time martingale remains a martingale on the natural-time grid
-- statement:
--   Restrict any continuous-index martingale to the integer time grid and the corresponding restricted filtration. Adaptedness and every conditional expectation identity follow by evaluating the original martingale at the embedded natural times.
-- source:
--   MeasureTheory.Martingale definition, pinned Mathlib Probability.Martingale.Basic. Formal bridge between continuous-time Lévy martingales and finite-grid optional stopping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.martingale_sample_nat
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {𝓖 : Filtration ℕ mΩ}
    (h𝓖 : ∀ n : ℕ, 𝓖 n = 𝓕 (n : ℝ≥0))
    (f : ℝ≥0 → Ω → ℝ)
    (hf : Martingale f 𝓕 μ) :
    Martingale (fun n : ℕ => f (n : ℝ≥0)) 𝓖 μ := by sorry
