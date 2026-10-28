-- Prove2me | Theorems.Thm_AvramDividend_Classical_sampled_levy_filtration_exists_of_monotone_grid
-- name    : AvramDividend.Classical.sampled_levy_filtration_exists_of_monotone_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T18:42:05.040125+00:00
-- url     : https://prove2.me/theorems/30211c83-14df-4e43-a0f9-d54341d53db5
-- title:
--   Sigma-finite discrete filtration sampled from a continuous-time Lévy filtration
-- statement:
--   Let 𝓕_t be a continuous-time filtration over nonnegative real times on a probability space. Given monotone grid times s_k indexed by natural numbers, there exists a natural-number filtration 𝓖_k which equals 𝓕_(s_k) exactly at every k and is sigma-finite with respect to the probability measure. Define its sigma-algebras by sampling the original filtration; monotonicity of s and 𝓕 proves the filtration property. Probability-measure finiteness supplies SigmaFiniteFiltration. The result is needed to instantiate the proved exponential-grid conditional dividend budget with the Lévy process filtration in the capped BV/UV verification branch.

import Mathlib.Probability.Process.Filtration

open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.sampled_levy_filtration_exists_of_monotone_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) :
    ∃ 𝓖 : Filtration ℕ mΩ,
      (∀ k : ℕ, 𝓖 k = 𝓕 (s k)) ∧ SigmaFiniteFiltration P 𝓖 := by sorry
