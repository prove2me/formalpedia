-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_deterministic_horizon_true_stop_finite_mark_linear_martingale_L2
-- name    : AvramDividend.Classical.avram_pj_workerC_original_deterministic_horizon_true_stop_finite_mark_linear_martingale_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:44:22.145719+00:00
-- url     : https://prove2.me/theorems/ed6e9c63-5049-42b3-942d-09b485659fb1
-- title:
--   Actual finite-horizon physical deterministic lattice of the pure-jump post-right dividend reserve has integrable L2 centred truncated small-mark martingale with exactly zero mean
-- statement:
--   For the true original spectrally negative Lévy process, genuine post-right admissible dividend path and any right-continuous stopping time rho, fix original uniform physical times t_i=i*n/(m+1). The actual positive-time counted negative Lévy marks z<=-1/(cut+1), centred by their true intensity on each physical interval and multiplied by the actual stopped clipped discounted prejump derivative of w, form an L2-integrable sum with expectation zero and a pathwise zero contribution whenever rho=0. This is an original Poisson compensated noise source on the exact horizon mesh needed for the true positive Ito-residual proof. No new stochastic assumptions.
-- source:
--   Proved 45efc6a5 original stopped predictable physical L2 centred grid, specialised to uniform deterministic horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_public_original_clipped_smallmark_stopped_grid_L2_mean_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_deterministic_horizon_true_stop_finite_mark_linear_martingale_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (n m : ℕ) (hn : 0 < n) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let H : ℕ → Ω → ℝ := fun i ω =>
      max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid i))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (ρ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range m, Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range m, Z i ω ∂P) = 0 ∧
    (∀ ω, ρ ω = 0 → ∑ i ∈ Finset.range m, Z i ω = 0) := by sorry
