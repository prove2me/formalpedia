-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_stopped_physical_Taylor_error_AE_measurable
-- name    : AvramDividend.Classical.avram_bv_error7_original_random_stopped_physical_Taylor_error_AE_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:06:42.414958+00:00
-- url     : https://prove2.me/theorems/c5740af2-ff0a-4978-9cda-5c15d5557d18
-- title:
--   Original BV sample-dependent stopped-grid Taylor error is a.e. measurable
-- statement:
--   On the original bounded-variation Lévy process X and original admissible dividend strategy D, the physical-grid C1 Taylor error with a measurable sample-dependent stopping index k and deterministic finite-grid envelope N is a.e. strongly measurable. Uses original process adaptedness, the original right-limit dividend and original compensated raw jump path evaluations, plus a proved general measurable masking lemma. Borel value and derivative assumptions are explicit.
-- source:
--   Source-exact original stochastic stopping prefix measurability adapter to BV-ERROR7; independent of signed BV prebudget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_stopped_index_masked_AE_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_random_stopped_physical_Taylor_error_AE_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hderiv : Measurable (deriv w))
    (q : ℝ) (u : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (k : ℕ → Ω → ℕ) (hk : ∀ m, Measurable (k m))
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
       ∑ i ∈ Finset.range (N m),
         if i < k m ω then
           Real.exp (-(q * (u m i : ℝ))) *
             (w (z i + c i) - w (z i) - deriv w (z i) * c i)
         else 0)) :
    ∀ m, AEStronglyMeasurable (Err m) P := by sorry
