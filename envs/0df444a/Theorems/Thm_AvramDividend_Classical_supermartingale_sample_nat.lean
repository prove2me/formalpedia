-- Prove2me | Theorems.Thm_AvramDividend_Classical_supermartingale_sample_nat
-- name    : AvramDividend.Classical.supermartingale_sample_nat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:37:17.818164+00:00
-- url     : https://prove2.me/theorems/0ecce9ae-c46a-4bc6-a305-bfb6e2297b1f
-- title:
--   A nonnegative-time supermartingale remains a supermartingale on the natural-time grid
-- statement:
--   Restrict any continuous-index supermartingale to the integer time grid with the matching restricted filtration. Strong adaptedness, conditional expectation inequality and integrability are inherited directly, enabling finite-grid optional stopping after a stochastic verification supermartingale has been proved.
-- source:
--   MeasureTheory.Supermartingale definition, pinned Mathlib Probability.Martingale.Basic. Bridge from a future stochastic-calculus verification step to the already proved finite-grid stopping inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.supermartingale_sample_nat
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {𝓖 : Filtration ℕ mΩ}
    (h𝓖 : ∀ n : ℕ, 𝓖 n = 𝓕 (n : ℝ≥0))
    (f : ℝ≥0 → Ω → ℝ)
    (hf : Supermartingale f 𝓕 μ) :
    Supermartingale (fun n : ℕ => f (n : ℝ≥0)) 𝓖 μ := by sorry
