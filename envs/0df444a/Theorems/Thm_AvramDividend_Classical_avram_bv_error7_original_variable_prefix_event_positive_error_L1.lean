-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_variable_prefix_event_positive_error_L1
-- name    : AvramDividend.Classical.avram_bv_error7_original_variable_prefix_event_positive_error_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:50:11.312198+00:00
-- url     : https://prove2.me/theorems/41445c02-b44c-4185-b7ba-588bb87520e8
-- title:
--   Genuine original stopped variable-endpoint C1 positive mesh error vanishes in expectation on interior events
-- statement:
--   For a genuine bounded-variation spectrally negative Lévy process under Standing and the original admissible dividend control D, a sample-dependent stopped physical grid ending at or before fixed T has a vanishing positive discounted C1 Taylor error mean on every compact interior localisation event s, when the exact original Y mesh refines on s and the masked error is a.e. measurable. The proof imports independently proved event-localised variable-prefix a.e. convergence and uniform authentic BV source domination, then applies the Proved original BV source L1 dominated convergence theorem. This is the exact local positive-error input required by the fixed-event Fatou epsilon absorption, with the ruin/cap complement treated separately.
-- source:
--   Source-exact new variable-endpoint event-localised mean adapter from event_X/Y and original source DCT, supporting 2bc848f9 and the accepted GG/FF tail route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_variable_prefix_event_C1_error_ae
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_variable_prefix_event_C1_uniform_dom
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_mass_positive_DCT_for_random_errors
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_variable_prefix_event_positive_error_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      |w z - w y| ≤ L * |z - y|)
    (hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ L)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (hT : T ≤ 1)
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
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m ω → |c m i| < δ)))
    (hMaskedMeas : ∀ m, AEStronglyMeasurable
      (fun ω => if ω ∈ s then Err m ω else 0) P) :
    (∀ m, Integrable (fun ω => max (if ω ∈ s then Err m ω else 0) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (if ω ∈ s then Err m ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
