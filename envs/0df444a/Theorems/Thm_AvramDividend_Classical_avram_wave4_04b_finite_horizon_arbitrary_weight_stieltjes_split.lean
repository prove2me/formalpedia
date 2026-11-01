-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_arbitrary_weight_stieltjes_split
-- name    : AvramDividend.Classical.avram_wave4_04b_finite_horizon_arbitrary_weight_stieltjes_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:15:05.934576+00:00
-- url     : https://prove2.me/theorems/b26d01a1-738d-4a8e-9ae2-6183fdbef741
-- title:
--   Every finite-horizon Stieltjes payoff weight splits into exact right-payment atoms and atomless control variation
-- statement:
--   For the actual adapted monotone Avram dividend strategy D, path ω and closed finite horizon [0,T], the restricted Lebesgue–Stieltjes measure is exactly a countable singleton-weighted atomic measure plus an atomless remainder. For every nonnegative extended-real payoff weight f, even a stopped-payment indicator times a discount factor, the entire weighted finite-horizon payoff splits exactly into the sum of true right-payment singleton masses times f and the full diffuse Stieltjes integral of f. Both singular-continuous and absolutely continuous parts remain; the time-zero and terminal atoms are retained. This is measure decomposition, not the Lévy stochastic Ito–Meyer formula.
-- source:
--   Exact finite-mass rightLimit identity for the actual source dividend measure, canonical atomic/diffuse decomposition, and Mathlib lintegral_add_measure/lintegral_sum_measure/lintegral_smul_measure/lintegral_dirac. It generalizes the already canonically Proved discounted finite-horizon equality by allowing arbitrary nonnegative weight.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_exists_atomic_diffuse_decomposition

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04b_finite_horizon_arbitrary_weight_stieltjes_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s : ℝ, f s ∂μ) =
      (∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) +
      (∫⁻ s : ℝ, f s ∂μdiffuse) := by sorry
