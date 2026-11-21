-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_fullmark_clipped_uniform_L2_from_predictability
-- name    : AvramDividend.Classical.avram_pj_workerC_original_fullmark_clipped_uniform_L2_from_predictability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T09:49:01.005227+00:00
-- url     : https://prove2.me/theorems/405b0764-034a-484b-8666-82537ba281d6
-- title:
--   Original fullmark stopped predictable derivative physical-grid diagonal L2 bound without extra integrability hypotheses
-- statement:
--   For the exact original spectrally negative Lévy process, admissible dividend strategy and true stopped marked grid, the original compensated finite negative-mark quadratic energy is uniformly at most K squared times horizon n and genuine mark intensity. Measurability and square integrability of each stopped clipped original prepayment derivative coefficient follow automatically from Proved original strong predictability and stopping time lemmas; no additional certificate hypothesis remains.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_fullmark_clipped_physical_grid_L2_uniform_energy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_stopped_predictable_clipped_grid_coefficient_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_fullmark_clipped_uniform_L2_from_predictability
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
    (∫ ω, ∑ i ∈ Finset.range m, (Z i ω)^2 ∂P) ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by sorry
