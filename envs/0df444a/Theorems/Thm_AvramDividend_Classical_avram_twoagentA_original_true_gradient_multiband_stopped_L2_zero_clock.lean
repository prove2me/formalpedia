-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_true_gradient_multiband_stopped_L2_zero_clock
-- name    : AvramDividend.Classical.avram_twoagentA_original_true_gradient_multiband_stopped_L2_zero_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T10:53:45.784056+00:00
-- url     : https://prove2.me/theorems/5baee2f9-f927-4702-9740-44e22752befd
-- title:
--   Actual stopped original-process clipped-gradient multiband negative-jump martingale is L2 centred and zero at zero clock
-- statement:
--   For any spectrally negative Lévy X, original dividend strategy D, same-space stopped clock, and finite family of negative jump annuli, the actual clipped discounted pre-jump gradient finite-grid compensated physical mark sum is L2 and has expectation zero and vanishes pathwise for zero clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_stopped_clipped_prejump_gradient_annulus_grid_L2_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_twoagentA_original_true_gradient_multiband_stopped_L2_zero_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (S : Finset ℕ) (cutLo cutHi : ℕ → ℕ)
    (hCut : ∀ i ∈ S, cutLo i ≤ cutHi i)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ j, grid j ≤ grid (j + 1))
    (n : ℕ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cutLo i : ℝ) + 1)))
        (-(1 / ((cutHi i : ℝ) + 1)))
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun i j ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s,
          X.X s ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
        (Ioc (grid j) (grid (j + 1)) ×ˢ B i)
    let r : ℕ → ℕ → ℝ := fun i j =>
      (((grid (j + 1) - grid j : ℝ≥0) : ℝ≥0∞) *
        X.ν (B i)).toReal
    let H : ℕ → Ω → ℝ := fun j ω =>
      max (-K) (min K (Real.exp (-(q * (grid j : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid j))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      ∑ j ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid j : WithTop ℝ≥0)
          then (0 : ℝ) else H j ω) * ((N i j ω).toReal - r i j)
    MemLp (fun ω => ∑ i ∈ S, Z i ω) 2 P ∧
      (∫ ω, ∑ i ∈ S, Z i ω ∂P) = 0 ∧
      (∀ ω, τ ω = 0 → ∑ i ∈ S, Z i ω = 0) := by sorry
