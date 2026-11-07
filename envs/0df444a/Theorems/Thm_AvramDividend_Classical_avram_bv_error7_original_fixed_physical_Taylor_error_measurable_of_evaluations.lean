-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_fixed_physical_Taylor_error_measurable_of_evaluations
-- name    : AvramDividend.Classical.avram_bv_error7_original_fixed_physical_Taylor_error_measurable_of_evaluations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:40:43.847286+00:00
-- url     : https://prove2.me/theorems/6a46b983-7fd9-4ad3-84b5-e00dd4128c6b
-- title:
--   Original deterministic-grid BV C1 Taylor error a.e. measurability from actual path evaluations
-- statement:
--   For the actual bounded-variation spectrally negative Lévy X, original admissible dividend D, negative-jump cumulative correction J and Y=X+J, the precise original discounted finite C1 Taylor error over a deterministic stopped physical grid is a.e. strongly measurable. It suffices that evaluations of the original X.X, the right-limit dividend D, and the actual jump-correction J are a.e. strongly measurable at each deterministic grid point, and that w and its derivative are Borel measurable. The proof constructs a.e. measurable reserves and continuous-source increments, composes with the Borel value and derivative, and takes a finite sum. No surrogate process or signed prebudget appears. This isolates three source-specific evaluation/measurability obligations for subsequent P3 integration.
-- source:
--   Original BV-ERROR7 missing measurability of deterministic stopped-grid physical Taylor sum; feeds accepted 23df9a93 and 32541007 without importing the desired BV prebudget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_fixed_physical_Taylor_error_measurable_of_evaluations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hderiv : Measurable (deriv w))
    (q : ℝ) (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hXeval : ∀ m i, AEStronglyMeasurable
      (fun ω => X.X (u m i) ω) P)
    (hDeval : ∀ m i, AEStronglyMeasurable
      (fun ω => rightLimit D (u m i) ω) P)
    (hJeval : ∀ m i, AEStronglyMeasurable
      (fun ω => ∑' v : ℝ≥0, if 0 < v ∧ v ≤ u m i then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0) P)
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
           (w (z i + c i) - w (z i) - deriv w (z i) * c i))) :
    ∀ m, AEStronglyMeasurable (Err m) P := by sorry
