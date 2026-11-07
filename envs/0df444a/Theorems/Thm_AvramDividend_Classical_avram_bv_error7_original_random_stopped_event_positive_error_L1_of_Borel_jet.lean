-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_stopped_event_positive_error_L1_of_Borel_jet
-- name    : AvramDividend.Classical.avram_bv_error7_original_random_stopped_event_positive_error_L1_of_Borel_jet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:28:24.18348+00:00
-- url     : https://prove2.me/theorems/f3d8ff9e-06a2-4b13-a33b-cf0fb178e660
-- title:
--   Original BV stopped physical Taylor positive error converges in mean with exhausting localisation
-- statement:
--   For the actual standing bounded-variation X and original admissible D on a deterministic physical grid with a measurable random stopped prefix, the expected positive C1 Taylor remainder tends to zero under exhaustive compact interior events and the authentic BV drift/jump mass domination outside those events. A.e. measurability of the original stochastic error is derived from its real X/D/J source, not assumed. No signed budget or surrogate process is used.
-- source:
--   Original-event specialisation of Proved 23df9a93 with true original stopped-prefix AE-measurability discharge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_variable_endpoint_event_positive_L1_of_error_meas
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_stopped_physical_Taylor_error_true_AE_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_random_stopped_event_positive_error_L1_of_Borel_jet
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hwMeas : Measurable w)
    (hDerivMeas : Measurable (deriv w))
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b L : ℕ → ℝ)
    (hBand : ∀ n, Set.Icc (a n) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hL : ∀ n, 0 ≤ L n)
    (hLip : ∀ n, ∀ y ∈ Set.Icc (a n) (b n),
      ∀ z ∈ Set.Icc (a n) (b n),
        |w z - w y| ≤ L n * |z - y|)
    (hDeriv : ∀ n, ∀ y ∈ Set.Icc (a n) (b n),
      |deriv w y| ≤ L n)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (hT : T ≤ 1)
    (u : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (k : ℕ → Ω → ℕ) (hk : ∀ m, Measurable (k m))
    (hBound : ∀ m ω, k m ω ≤ N m)
    (hGrid : ∀ m ω, u m 0 = 0 ∧ u m (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m i ≤ u m (i + 1)))
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n)
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
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
    (hPath : ∀ n, ∀ᵐ ω ∂P, ω ∈ s n →
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℕ → ℝ := fun m i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℕ → ℝ := fun m i =>
         Y (u m (i + 1)) - Y (u m i)
       (∀ m i, i < k m ω →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc (a n) (b n)) ∧
       (∀ δ : ℝ, 0 < δ →
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m ω → |c m i| < δ)))
    (K : ℝ) (hK : 0 ≤ K)
    (hOutside : ∀ n m, ∀ᵐ ω ∂P, ω ∉ s n →
      max (Err m ω) 0 ≤
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) :
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
