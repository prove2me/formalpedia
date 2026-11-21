-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_stopped_fullnegative_physical_grid_any_event_restricted_L1_budget
-- name    : AvramDividend.Classical.avram_pj_original_stopped_fullnegative_physical_grid_any_event_restricted_L1_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T17:46:34.372814+00:00
-- url     : https://prove2.me/theorems/6a7e1167-8857-4c7e-911b-85db5890fb63
-- title:
--   Actual original full negative Lévy stopped physical-grid compensated sum eventwise L1 budget
-- statement:
--   For the actual original spectrally negative Levy full negative-mark compensated stopped physical grid with true physical clipped discounted prepayment derivative, on every measurable event the L1 integral of the complete genuine grid sum is bounded by the square root of K squared times horizon n times actual Levy finite negative-mark intensity, whenever the true fullsum absolute value is integrable. This follows from the proved global original fullmark L1 estimate 6faab04c and monotonicity of nonnegative integrals under event restriction, retaining all cross-cell covariances and exact original stopping and marks.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_stopped_fullnegative_marked_grid_fullsum_uniform_L1_budget
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_stopped_fullnegative_physical_grid_any_event_restricted_L1_budget
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
    ∀ A : Set Ω, MeasurableSet A →
      Integrable (fun ω => |∑ i ∈ Finset.range m, Z i ω|) P →
    (∫ ω in A, |∑ i ∈ Finset.range m, Z i ω| ∂P) ≤
      Real.sqrt (K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal)) := by sorry
