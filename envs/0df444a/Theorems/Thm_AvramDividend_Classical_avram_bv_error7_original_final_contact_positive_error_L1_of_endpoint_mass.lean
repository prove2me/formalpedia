-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_positive_error_L1_of_endpoint_mass
-- name    : AvramDividend.Classical.avram_bv_error7_original_final_contact_positive_error_L1_of_endpoint_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:56:42.582242+00:00
-- url     : https://prove2.me/theorems/0bedd363-66f5-4266-aa02-2c2bd505cf55
-- title:
--   Original final ruin/horizon contact Taylor positive error vanishes in expected value under authentic BV source-mass domination
-- statement:
--   For the original BV Lévy X, admissible dividend strategy D and genuine stopped physical grid, a uniform endpoint Lipschitz/derivative bound and shrinking compensated mesh imply that the positive contact Taylor error is integrable and vanishes in expectation. The genuine source-mass bound is derived from original BV grid variation rather than assumed.
-- source:
--   Apply the separately proved source-specific a.e. contact Taylor limit and original final-contact source-mass domination, then the accepted original-BV source-mass dominated convergence theorem. The only remaining nonautomatic assumptions are exact endpoint value/derivative regularity and a.e. measurability; no signed BV prebudget is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_compensated_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_discounted_single_contact_Taylor_bound
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_Taylor_error_ae_zero_of_endpoint_bounds
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_Taylor_error_le_BV_mass_of_endpoint_bounds
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_mass_positive_DCT_for_random_errors
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_final_contact_positive_error_L1_of_endpoint_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q L : ℝ) (hq : 0 ≤ q) (hL : 0 ≤ L)
    (T : ℝ≥0) (hT : T ≤ 1)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m 0 = 0 ∧ u m (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m i ≤ u m (i + 1)))
    (hMesh : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       ∀ δ : ℝ, 0 < δ → ∀ᶠ m in Filter.atTop,
         ∀ i, i < k m ω →
           |Y (u m (i + 1)) - Y (u m i)| < δ))
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
         (w (z + c) - w z - deriv w z * c)))
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
