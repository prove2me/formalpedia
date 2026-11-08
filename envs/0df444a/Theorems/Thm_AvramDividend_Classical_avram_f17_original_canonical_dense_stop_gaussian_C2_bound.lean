-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f17_original_canonical_dense_stop_gaussian_C2_bound
-- name    : AvramDividend.Classical.avram_f17_original_canonical_dense_stop_gaussian_C2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:02:26.837014+00:00
-- url     : https://prove2.me/theorems/1ac31635-e5a5-4350-8466-0eef0b51523f
-- title:
--   Canonical dense-sequence original bounded stop supplies quantitative discounted Gaussian left-reserve C2 bounds
-- statement:
--   For the actual original zero-jump unbounded-variation Lévy process, use Mathlib's canonical dense sequence of nonnegative times to define the bounded interior exit stopping clock. This clock is an original right-continuous-filtration stopping time and produces globally time-uniform deterministic discounted gradient and Hessian bounds for the exact left reserve limit before the stop. No externally supplied grid or dense-range hypothesis remains.
-- source:
--   Direct canonical dense-grid specialisation of the public genuine original bounded stopping-time and quantitative left-limit Gaussian source theorem. Uses pinned TopologicalSpace.denseRange_denseSeq; no private source imports and no stochastic surrogate.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f17_original_dense_bounded_stop_exact_gaussian_C2_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f17_original_canonical_dense_stop_gaussian_C2_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (B : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω =>
      min (⨅ k : ℕ,
        if x + X.X ((TopologicalSpace.denseSeq ℝ≥0) k) ω -
            rightLimit D ((TopologicalSpace.denseSeq ℝ≥0) k) ω < lower ∨
              upper < x + X.X ((TopologicalSpace.denseSeq ℝ≥0) k) ω -
                rightLimit D ((TopologicalSpace.denseSeq ℝ≥0) k) ω
        then ((TopologicalSpace.denseSeq ℝ≥0) k : WithTop ℝ≥0) else ⊤)
        (B : WithTop ℝ≥0)) ∧
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤ min (⨅ k : ℕ,
          if x + X.X ((TopologicalSpace.denseSeq ℝ≥0) k) ω -
              rightLimit D ((TopologicalSpace.denseSeq ℝ≥0) k) ω < lower ∨
                upper < x + X.X ((TopologicalSpace.denseSeq ℝ≥0) k) ω -
                  rightLimit D ((TopologicalSpace.denseSeq ℝ≥0) k) ω
          then ((TopologicalSpace.denseSeq ℝ≥0) k : WithTop ℝ≥0) else ⊤)
          (B : WithTop ℝ≥0) →
        ∀ t : ℝ≥0, 0 < t → t < T →
          let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
          y ∈ Set.Icc lower upper ∧
            |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG ∧
            |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ KH := by sorry
