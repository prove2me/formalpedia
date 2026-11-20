-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_sigma_family_clipped_smallmark_L2_centered
-- name    : AvramDividend.Classical.avram_jump6_B_original_canonical_sigma_family_clipped_smallmark_L2_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:19:48.050018+00:00
-- url     : https://prove2.me/theorems/81c334ef-ac5f-4b84-a18c-196a14baf770
-- title:
--   Original canonical physical clock negative mark cutoffs: stopped clipped small-jump centred L2 and zero-clock all sigma-family
-- statement:
--   For every actual subordinate right-continuous stopping time sigma(k), every canonical physical-grid resolution j, arbitrary cutoff and finite grid length n, the genuine original negative jump marked count-minus-compensator with bounded clipped discounted pre-jump gradient is L2, has expectation zero, and vanishes at sigma(k)=0. The grid is exactly i/(j+1), as in the original infinite-activity Ito source; no finite-activity, surrogate process or additional stochastic coupling is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_public_original_clipped_smallmark_stopped_grid_L2_mean_zero
set_option autoImplicit false
open MeasureTheory Set Filter ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_canonical_sigma_family_clipped_smallmark_L2_centered
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
    (∀ ω, τ ω = 0 → ∑ i ∈ Finset.range n, Z i ω = 0) := by sorry
