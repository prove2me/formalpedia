-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_positive_clock_centered_without_event_assumption
-- name    : AvramDividend.Classical.avram_jump6_B_original_canonical_positive_clock_centered_without_event_assumption
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:42:17.210306+00:00
-- url     : https://prove2.me/theorems/3e6864ac-b8d1-4be1-afbe-8ebb1a4f7f0f
-- title:
--   Original canonical clipped stopped negative-jump compensation has zero positive-clock mean without any added event measurability premise
-- statement:
--   For the actual original spectrally negative Levy process, the same canonical physical-grid stopped clipped negative-jump count-minus-compensator is square-integrable, mean-zero globally and on the strictly positive subordinate stopping-clock event, and exactly zero at clock zero. The positive-clock event measurability follows directly from the supplied IsStoppingTime hypothesis by the public zero-event theorem, rather than being added as a new hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_sigma_family_clipped_smallmark_L2_centered
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_positive_clock_centered_integral_of_zero_complement
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
set_option autoImplicit false
open MeasureTheory Set Filter ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_canonical_positive_clock_centered_without_event_assumption
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (sigmaSeq : ℕ → Ω → ℝ≥0)
    (hSigmaStop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (sigmaSeq k ω : WithTop ℝ≥0)))
    (j k n : ℕ) :
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
