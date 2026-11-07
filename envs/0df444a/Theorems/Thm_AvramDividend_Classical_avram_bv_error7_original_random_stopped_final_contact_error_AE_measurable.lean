-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_stopped_final_contact_error_AE_measurable
-- name    : AvramDividend.Classical.avram_bv_error7_original_random_stopped_final_contact_error_AE_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:29:52.811742+00:00
-- url     : https://prove2.me/theorems/1e268091-14ff-4f31-9a55-f5f7f748ff09
-- title:
--   True original random-stopped final contact Taylor error is measurable as full minus strict prefix
-- statement:
--   For the original Lévy X, admissible dividend D, measurable random stopped index k, and literal full and strict physical Taylor sources, the true final contact remainder, defined as the difference of those two sources, is a.e. measurable. The zero-clock case is included.
-- source:
--   Apply the previously Proved original true stopped-prefix measurability theorem separately at k and k-1, deriving measurability and the envelope bound for the strict count. Their difference is a.e. measurable. The independent exact contact-cell Finset identity identifies this difference with the unique final Taylor cell, avoiding primitive random evaluation measurability at k-1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_stopped_physical_Taylor_error_true_AE_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_random_stopped_final_contact_error_AE_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hwMeas : Measurable w)
    (hDerivMeas : Measurable (deriv w)) (q : ℝ)
    (u : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (k : ℕ → Ω → ℕ) (hk : ∀ m, Measurable (k m))
    (hBound : ∀ m ω, k m ω ≤ N m)
    (ErrFull ErrStrict : ℕ → Ω → ℝ)
    (hFull : ∀ m ω, ErrFull m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       let g : ℕ → ℝ := fun i =>
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)
       ∑ i ∈ Finset.range (k m ω), g i))
    (hStrict : ∀ m ω, ErrStrict m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       let g : ℕ → ℝ := fun i =>
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)
       ∑ i ∈ Finset.range (k m ω - 1), g i)) :
    ∀ m, AEStronglyMeasurable
      (fun ω => ErrFull m ω - ErrStrict m ω) P := by sorry
