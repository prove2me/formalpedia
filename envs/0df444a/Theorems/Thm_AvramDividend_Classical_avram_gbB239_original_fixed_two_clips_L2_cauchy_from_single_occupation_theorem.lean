-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB239_original_fixed_two_clips_L2_cauchy_from_single_occupation_theorem
-- name    : AvramDividend.Classical.avram_gbB239_original_fixed_two_clips_L2_cauchy_from_single_occupation_theorem
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T08:42:20.826097+00:00
-- url     : https://prove2.me/theorems/175c1e37-df48-4480-8e7e-550e9715cc29
-- title:
--   Original zero-jump finite-cap Gaussian physical grid fixed levels are two-mesh L2 Cauchy from the fixed-level occupation theorem
-- statement:
--   For the original zero-jump unbounded-variation Lévy source and real dividend strategy, at any two fixed clipping levels on which the clipped derivative is continuous through the closed band, the exact discounted stopped physical-time mesh coefficients are two-mesh L2 Cauchy. Uses only the still-open B100 fixed-level null occupation theorem twice at deterministic n plus the already Proved B80 original countable discontinuities and B238 generic fixed-level convergence.
-- source:
--   Direct original B65 parent route: B100 → B239 → B65, avoiding selected cutoff perturbation and B227 direct if B100 proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB239_original_fixed_two_clips_L2_cauchy_from_single_occupation_theorem
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (hn : 0 < n) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (a b : ℝ) (ρ : Ω → ℝ≥0)
    (hρ : Measurable ρ)
    (hDeriv : ∀ y ∈ Set.Ioo a b, ContinuousAt (deriv w) y)
    (hClosed : ContinuousOn (deriv w) (Set.Icc a b)) :
    let Y : ℝ≥0 → Ω → ℝ := fun s ω =>
      x + X.X s ω - rightLimit D s ω
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ)
        then if (s : ℝ) < (ρ ω : ℝ) then
          Real.exp (-(q * (s : ℝ))) *
            (if Y (Real.toNNReal (s : ℝ)) ω ∈ Set.Icc a b
              then deriv w (Y (Real.toNNReal (s : ℝ)) ω) else 1)
        else 0 else 0)
    Tendsto (fun mp : ℕ × ℕ =>
      ∫ t in Set.Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K mp.1 t ω - K mp.2 t ω)^2 ∂P) ∂volume)
      atTop (𝓝 (0 : ℝ)) := by sorry
