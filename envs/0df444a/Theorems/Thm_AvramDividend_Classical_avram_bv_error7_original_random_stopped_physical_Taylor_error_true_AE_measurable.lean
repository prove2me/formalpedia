-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_stopped_physical_Taylor_error_true_AE_measurable
-- name    : AvramDividend.Classical.avram_bv_error7_original_random_stopped_physical_Taylor_error_true_AE_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:16:49.120398+00:00
-- url     : https://prove2.me/theorems/d4d33173-2445-4d5a-9ea5-dcc42a66bc0f
-- title:
--   Original BV physical-grid true randomly stopped Taylor sum is a.e. measurable
-- statement:
--   For the actual standing bounded-variation X and original admissible D, with Borel w and derivative and deterministic grid u, the discounted C1 Taylor error summed over the true random prefix k m ω is a.e. strongly measurable given a measurable k bounded by deterministic N. The proof uses original X/D/J evaluations and the exact random-prefix measurability theorem; no assumed error measurability.
-- source:
--   The original Lévy process's adaptedness, original dividend-strategy right-limit measurability and the proved original BV raw-jump cumulative measurability give measurable physical-grid source cell coefficients. The accepted exact random-prefix measurability lemma then establishes a.e. strong measurability of the true physical-grid Taylor sum up to a measurable, bounded sample-dependent stopping index. No BV prebudget or surrogate process is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_measurable_random_stopped_prefix_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_random_stopped_physical_Taylor_error_true_AE_measurable
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
    (hBound : ∀ m ω, k m ω ≤ N m)
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
       ∑ i ∈ Finset.range (k m ω),
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i))) :
    ∀ m, AEStronglyMeasurable (Err m) P := by sorry
