-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_physical_C1_positive_error_L1_any_clock
-- name    : AvramDividend.Classical.avram_p3_comp8_original_physical_C1_positive_error_L1_any_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:17:22.42887+00:00
-- url     : https://prove2.me/theorems/0bd3dc5b-f0bd-4720-8990-6fb2914ed13d
-- title:
--   Original physical-grid positive C1 source error converges in L1 for any finite horizon under BV domination
-- statement:
--   Generalises the published BV-ERROR7 positive-error L1 adapter from T≤1 to arbitrary finite T. Err is syntactically tied to the original X, D, jump-removed source path and actual stopped physical grid Taylor cells; if those errors converge almost surely and are uniformly dominated by a scalar multiple of the original finite-horizon BV source mass, their positive parts are integrable and have expectations tending to zero.
-- source:
--   Source-faithful adaptation of Proved theorem 70a2660b: replace the single T≤1 integrable source envelope premise with the derived all-horizon original BV source mass theorem, all other terms unchanged.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_mass_integrable_any_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual original X/D discounted Taylor cell error has a vanishing
positive expected part as soon as it is controlled by the genuine BV L1 mass. -/

theorem AvramDividend.Classical.avram_p3_comp8_original_physical_C1_positive_error_L1_any_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       ∑ i ∈ Finset.range (k m),
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
    (K : ℝ) (hK : 0 ≤ K)
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P)
    (hErrAE : ∀ᵐ ω ∂P,
      Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)))
    (hDom : ∀ m, ∀ᵐ ω ∂P,
      ‖Err m ω‖ ≤ K * (|X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|)) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
