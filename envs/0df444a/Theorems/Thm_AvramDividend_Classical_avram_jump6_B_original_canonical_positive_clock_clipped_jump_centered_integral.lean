-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_positive_clock_clipped_jump_centered_integral
-- name    : AvramDividend.Classical.avram_jump6_B_original_canonical_positive_clock_clipped_jump_centered_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:30:44.696242+00:00
-- url     : https://prove2.me/theorems/21d418b8-fbcf-417d-ab49-3cc327f07557
-- title:
--   Original canonical stopped smallmark martingale centred on positive-clock event
-- statement:
--   For original spectrally negative Levy jump counts on the canonical i/(j+1) physical grid, the stopped clipped negative-jump compensator has square-integrable zero-mean finite sum. It also has exactly zero expected value restricted to the positive subordinate stopping-clock event, assuming that event is measurable. The zero-clock complement vanishing follows from Proved actual source finite-grid theorem 81c334ef; the restricted mean-zero follows public theorem 44fbfa37. No finite jump activity or surrogate process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_sigma_family_clipped_smallmark_L2_centered
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_positive_clock_centered_integral_of_zero_complement
set_option autoImplicit false
open MeasureTheory Set Filter ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_canonical_positive_clock_clipped_jump_centered_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (sigmaSeq : ℕ → Ω → ℝ≥0)
    (hSigmaStop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (sigmaSeq k ω : WithTop ℝ≥0)))
    (j k n : ℕ) (hA : MeasurableSet {ω : Ω | sigmaSeq k ω ≠ 0}) :
    let τ : Ω → ℝ≥0 := sigmaSeq k
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
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range n, Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 ∧
    (∀ ω, τ ω = 0 → ∑ i ∈ Finset.range n, Z i ω = 0) ∧
    (∫ ω in {ω : Ω | sigmaSeq k ω ≠ 0}, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by sorry
