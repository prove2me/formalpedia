-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_subclock_canonical_grid_fullmark_compensated_L2_centered
-- name    : AvramDividend.Classical.avram_jump6_B_original_subclock_canonical_grid_fullmark_compensated_L2_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:13:34.310258+00:00
-- url     : https://prove2.me/theorems/016c0f75-a6df-47a5-b67e-32a4e6780661
-- title:
--   Actual original subclock canonical mesh compensated full negative-mark L2 and exact mean-zero with zero-clock support
-- statement:
--   The original spectrally negative Levy jump random measure, original right-limit dividend D, and arbitrary stopped subclocks sigma(k) yield a finite-horizon full negative-cutoff compensated jump mesh with L2 integrability, exactly zero mean and pathwise zero support when sigma(k)=0. The physical grid is the exact Jump6 i/(j+1) grid, and the finite sum includes the actual (horizon+1)(j+1) cells. No finite-activity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_uniform_physical_stopped_fullmark_L2_mean_zero
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_subclock_canonical_grid_fullmark_compensated_L2_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (j horizon k : ℕ) :
    let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
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
      (if (σ k ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range ((horizon + 1) * (j + 1)), Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range ((horizon + 1) * (j + 1)), Z i ω ∂P) = 0 ∧
    (∀ ω, σ k ω = 0 → ∑ i ∈ Finset.range ((horizon + 1) * (j + 1)), Z i ω = 0) := by sorry
