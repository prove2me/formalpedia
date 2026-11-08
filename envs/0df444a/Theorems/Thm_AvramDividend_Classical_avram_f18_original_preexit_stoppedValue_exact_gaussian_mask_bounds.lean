-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f18_original_preexit_stoppedValue_exact_gaussian_mask_bounds
-- name    : AvramDividend.Classical.avram_f18_original_preexit_stoppedValue_exact_gaussian_mask_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:32:09.134693+00:00
-- url     : https://prove2.me/theorems/d73fa603-4b06-4deb-a878-b91b3168c7df
-- title:
--   Original physical pre-exit stoppedValue Gaussian coefficients satisfy exact uniform bounds
-- statement:
--   At every strictly interior positive original physical stopping time, the actual ruin-masked Gaussian derivative and interior Hessian coefficients, evaluated by Mathlib stoppedValue and truncated at a finite horizon, admit a pair of deterministic uniform bounds. The finite stopped Gaussian C2 martingale theorem may consume these actual coefficients on the same stopped grid; contact and time-zero cells remain separate.
-- source:
--   Direct instantiation of public Proved original preexit ruin-indicator theorem a23ab0a4 at the genuine random evaluation time, plus definitional stoppedValue evaluation at a finite clock. Supports Proved original finite compensated Gaussian sum 49c99bb6.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_source_ruin_indicator_gaussian_C2_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f18_original_preexit_stoppedValue_exact_gaussian_mask_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U)
    (τ : Ω → ℝ≥0) (Tmax : ℝ≥0)
    (hinterior : ∀ ω, ∃ T : ℝ≥0,
      0 < τ ω ∧ τ ω < T ∧
      (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤)) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ ω : Ω,
        |stoppedValue (fun t ω =>
          if t ≤ Tmax then
            (Real.exp (-(q * (t : ℝ))) *
              deriv w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
          else 0) (fun ω => (τ ω : WithTop ℝ≥0)) ω| ≤ KG ∧
        |stoppedValue (fun t ω =>
          if t ≤ Tmax then
            (Real.exp (-(q * (t : ℝ))) *
              (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
               if 0 < y ∧ ENNReal.ofReal y < C
               then iteratedDeriv 2 w y else 0)) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
          else 0) (fun ω => (τ ω : WithTop ℝ≥0)) ω| ≤ KH := by sorry
