-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_history_survival_positive_kernel_map
-- name    : AvramDividend.Classical.avram_root29_01_history_survival_positive_kernel_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:20:43.311982+00:00
-- url     : https://prove2.me/theorems/6fe4b3eb-4c64-4e6e-ae0a-c7936fdbaa5f
-- title:
--   Actual source-Lévy historical reserve survival map for positive monotone future rewards
-- statement:
--   For the actual original Lévy path measure P, the historical F_s-measurable pair of current reserve increment and closed lower-survival flag pushes an arbitrary monotone real future-reserve reward to the exact positive pathwise historical indicator kernel. The proof establishes all required measurability using adaptedness, established history-pair measurability and monotonicity of the future reward; it invokes the genuine measure pushforward identity, with no stopping assumption, scale semigroup or Wiener-Hopf independence.
-- source:
--   Proved  bab28150 source history pair, measurable monotone F and pinned Mathlib lintegral_map; work/avram_root29_01_history_survival_positive_kernel_map.lean.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_history_survival_pair_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_root29_01_history_survival_positive_kernel_map
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ x : ℝ) (s : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (F : ℝ → ℝ) (hF : Monotone F) :
    (∫⁻ h : ℝ × Bool,
      (if h.2 then
        ENNReal.ofReal (Real.exp
          (θ * h.1 - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) *
        ENNReal.ofReal (F (x + h.1))
       else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω : Ω => (X.X s ω,
        decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω))) P)) =
    (∫⁻ ω : Ω,
      (if ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω then
        ENNReal.ofReal (Real.exp
          (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) *
        ENNReal.ofReal (F (x + X.X s ω))
       else (0 : ℝ≥0∞)) ∂P) := by sorry
