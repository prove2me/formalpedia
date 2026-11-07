-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_Taylor_error_le_BV_mass_of_endpoint_bounds
-- name    : AvramDividend.Classical.avram_bv_error7_original_final_contact_Taylor_error_le_BV_mass_of_endpoint_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:47:46.644886+00:00
-- url     : https://prove2.me/theorems/e2f1efc8-5d31-4cbe-9d6d-e3d83f9b7923
-- title:
--   Original final contact Taylor remainder dominated by actual integrable BV source mass
-- statement:
--   The authentic original BV stopped physical-grid final ruin/horizon contact Taylor error is uniformly dominated in absolute value by 2L times the source mass |drift|T+|drift T-X_T|, under only an explicit one-cell endpoint Lipschitz bound and derivative bound. The contact cell may touch the cap or ruin and k=0 is handled exactly.
-- source:
--   Combine the Proved original source-specific contact-cell variation bound and the discounted scalar Taylor inequality, preserving the actual X,D,J,Y, random stopped index and original horizon T. The domination is uniform across grid level and sample and uses no canonical BV prebudget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_discounted_single_contact_Taylor_bound
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_compensated_increment_le_BV_mass
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_final_contact_Taylor_error_le_BV_mass_of_endpoint_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q L : ℝ) (hq : 0 ≤ q) (hL : 0 ≤ L)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m 0 = 0 ∧ u m (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m i ≤ u m (i + 1)))
    (hContact : ∀ m ω, k m ω ≠ 0 →
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℝ := x + X.X (u m (k m ω - 1)) ω -
         rightLimit D (u m (k m ω - 1)) ω
       let c : ℝ := Y (u m (k m ω)) - Y (u m (k m ω - 1))
       |w (z + c) - w z| ≤ L * |c| ∧ |deriv w z| ≤ L))
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℝ := x + X.X (u m (k m ω - 1)) ω -
         rightLimit D (u m (k m ω - 1)) ω
       let c : ℝ := Y (u m (k m ω)) - Y (u m (k m ω - 1))
       if k m ω = 0 then 0
       else Real.exp (-(q * (u m (k m ω - 1) : ℝ))) *
         (w (z + c) - w z - deriv w z * c))) :
    ∀ m, ∀ᵐ ω ∂P,
      ‖Err m ω‖ ≤ (2 * L) * (|X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) := by sorry
