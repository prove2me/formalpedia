-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_variable_prefix_event_C1_error_ae
-- name    : AvramDividend.Classical.avram_bv_error7_original_variable_prefix_event_C1_error_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:45:48.76416+00:00
-- url     : https://prove2.me/theorems/f6d44aa3-a01b-422b-9374-ba590d7ec2d8
-- title:
--   Original variable-horizon BV C1 Taylor error vanishes on each compact interior localisation event
-- statement:
--   For the genuine original bounded-variation spectrally negative Lévy X and original admissible D, let sample-dependent physical grids finish at any time at most fixed T. If the exact Taylor cells lie in a compact strict interior band and the actual jump-removed source mesh refines on a given stochastic localisation event s, then the authentic original discounted C1 Taylor error masked to s converges to zero almost surely. The proof uses the newly proved fixed-horizon uniform source variation budget for every variable-endpoint prefix and the already proved global C1 Taylor modulus; outside s the error is identically zero. This supports the event-localised positive error L1 bridge to the original stopped-grid Fatou certificate, without requiring compact interior cells on ruin/cap boundary paths.
-- source:
--   Exact variable-endpoint strengthening of previously Proved BV-ERROR7 event_X using Proved 2a0c3e31 and 23921613. Needed by 2bc848f9 and prior event localisation/Fatou chain.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_prefix_Y_variation_le_full_horizon_mass
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_variable_prefix_event_C1_error_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (u : ℕ → Ω → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m ω 0 = 0 ∧ u m ω (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m ω i ≤ u m ω (i + 1)))
    (s : Set Ω)
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m ω i) ω - rightLimit D (u m ω i) ω
       let c : ℕ → ℝ := fun i => Y (u m ω (i + 1)) - Y (u m ω i)
       ∑ i ∈ Finset.range (k m ω),
         Real.exp (-(q * (u m ω i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
    (hPath : ∀ᵐ ω ∂P, ω ∈ s →
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℕ → ℝ := fun m i =>
         x + X.X (u m ω i) ω - rightLimit D (u m ω i) ω
       let c : ℕ → ℕ → ℝ := fun m i =>
         Y (u m ω (i + 1)) - Y (u m ω i)
       (∀ m i, i < k m ω →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) ∧
       (∀ δ : ℝ, 0 < δ →
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m ω → |c m i| < δ))) :
    ∀ᵐ ω ∂P, Tendsto
      (fun m => if ω ∈ s then Err m ω else 0) atTop (nhds (0 : ℝ)) := by sorry
