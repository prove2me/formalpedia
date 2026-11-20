-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_stopped_uniform_L2_mean_and_energy_v2
-- name    : AvramDividend.Classical.avram_pj_workerC_original_stopped_uniform_L2_mean_and_energy_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:40:47.663001+00:00
-- url     : https://prove2.me/theorems/1084f74c-9a9a-4d9c-aaf4-382940880b6e
-- title:
--   Exact original stopped finite physical jump L2 mean and energy
-- statement:
--   Combine publicly Proved true original truncated negative-mark stopped physical-grid compensated mean-zero L2 and exact original squared-energy intensity identities, on the same deterministic n/(m+1) physical grid and post-right dividend reserve.
-- source:
--   Proved ed6e9c63 original stopped L2 centered finite mark and ddd39364 original exact stopped full cutoff L2 diagonal energy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_deterministic_horizon_true_stop_finite_mark_linear_martingale_L2
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_true_uniform_physical_stopped_discounted_negative_mark_diagonal_L2_energy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_stopped_uniform_L2_mean_and_energy_v2
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
    (∀ ω, ρ ω = 0 → ∑ i ∈ Finset.range m, Z i ω = 0) ∧
        Integrable (fun ω => ∑ i ∈ Finset.range m, (Z i ω)^2) P ∧
      (∫ ω, ∑ i ∈ Finset.range m, (Z i ω)^2 ∂P) =
        ∑ i ∈ Finset.range m,
          r i * ∫ ω, (if (ρ ω : WithTop ℝ≥0) ≤
            (grid i : WithTop ℝ≥0) then (0 : ℝ)
            else H i ω)^2 ∂P := by sorry
