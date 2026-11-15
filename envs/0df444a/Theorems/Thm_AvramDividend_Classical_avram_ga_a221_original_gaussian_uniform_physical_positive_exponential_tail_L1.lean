-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a221_original_gaussian_uniform_physical_positive_exponential_tail_L1
-- name    : AvramDividend.Classical.avram_ga_a221_original_gaussian_uniform_physical_positive_exponential_tail_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:57:28.795196+00:00
-- url     : https://prove2.me/theorems/bf7a9332-18f9-42d5-829f-063351179fa1
-- title:
--   Original zero-jump Gaussian finite physical mesh expected positive exponential large increment tails vanish
-- statement:
--   For original zero jump Gaussian Lévy source increments taken on any deterministic finite grid of width n/(m+1), the finite grid positive tilted normalised-centred Gaussian large-increment exponential tail sum has expectation converging to zero. Uses source adapted measurability and exact Gaussian exponential integrability, not a surrogate Brownian process, feeding the original a216 combined large cell source.
-- source:
--   Original source Gaussian a68 integrable exp, a220 Chernoff and a218 finite expected sum L1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a227_original_gaussian_normalised_positive_exponential_tail_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a218_gaussian_chernoff_uniform_finite_mesh_integral_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a220_original_gaussian_mesh_one_cell_positive_exponential_chernoff
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a221_original_gaussian_uniform_physical_positive_exponential_tail_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (hn : 0 < n) (s t : ℕ → ℕ → ℝ≥0)
    (hst : ∀ m i, i < m → s m i ≤ t m i)
    (hWidth : ∀ m i, i < m →
      (((t m i - s m i : ℝ≥0) : ℝ)) =
        (n : ℝ) / ((m : ℝ) + 1))
    (θ δ : ℝ) (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    Tendsto (fun m : ℕ =>
      ∫ ω, (∑ i ∈ Finset.range m,
        let Z : ℝ := ((X.X (t m i) ω - X.X (s m i) ω) -
          ((t m i - s m i : ℝ≥0) : ℝ) * X.c) / X.σ
        if δ ≤ Z then Real.exp (θ * Z) else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
