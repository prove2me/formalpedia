-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a274_original_gaussian_true_physical_signed_exponential_tail_pointwise_majorant
-- name    : AvramDividend.Classical.avram_ga_a274_original_gaussian_true_physical_signed_exponential_tail_pointwise_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:23:23.188265+00:00
-- url     : https://prove2.me/theorems/f477a472-a963-443f-bc84-d2fd33feb5fe
-- title:
--   Original stopped Gaussian signed rare exponential fullcell sum bounded by true positive Gaussian exponential and stopped prefix raw quadratic tails
-- statement:
--   For the actual original Gaussian Lévy process physical grid and arbitrary stopping time rho, the exact wholly pre-stop sum of exp(theta times raw increment) over both rare increment tails |r|≥δ is pointwise bounded by the positive rare raw exponential fullcell sum and δ^-2 times the stopped prefix raw large-square sum. The result uses a271 finite mask decomposition and only the positive pathwise inclusion of fullcell masks in prefix masks. It aligns exactly with the already Proved original a233 positive Gaussian exponential expected L1 and a187 prefix raw large-square expected L1, the two decisive sources for the original combined a263 large residual.
-- source:
--   Exact original X.X fullcell gaussian a271 + prefix domination; a233/a187 original source expected L1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a271_masked_fullcell_rare_signed_Gaussian_exponential_sum_dominated
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a274_original_gaussian_true_physical_signed_exponential_tail_pointwise_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (theta delta : ℝ) (hθ : 0 ≤ theta) (hδ : 0 < delta) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0)+1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0)*Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i+Δ m) ω-X.X (s m i) ω
    let Signed : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ |R m i ω|
        then Real.exp (theta*R m i ω) else 0
    let Positive : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ R m i ω
        then Real.exp (theta*R m i ω) else 0
    let Square : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if s m i < ρ ω then
          (if delta ≤ |R m i ω| then (R m i ω)^2 else 0)
        else 0
    ∀ m ω, Signed m ω ≤ Positive m ω+(1/delta^2)*Square m ω := by sorry
