-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_variable_prefix_event_C1_uniform_dom
-- name    : AvramDividend.Classical.avram_bv_error7_original_variable_prefix_event_C1_uniform_dom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:40:10.298026+00:00
-- url     : https://prove2.me/theorems/1d611e68-e3c7-4f5b-81f8-fd91abd1318c
-- title:
--   Original variable-horizon BV source mass dominates compact-event C1 Taylor error
-- statement:
--   For the actual original BV Lévy source X and admissible D, the absolute discounted C1 Taylor error on any sample-dependent physical prefix ending before T and masked to an interior localisation event is bounded uniformly by 2L times the original fixed-T BV source mass, provided the exact Taylor segments remain in the compact band on the localisation event. This follows from the independently proved variable-prefix original C1 source bound 24aa95b9, with no requirements outside the event and no signed prebudget. It is the uniform integrable domination needed for the original event-localised positive-error DCT.
-- source:
--   Variable-endpoint strengthening of previously Proved BV-ERROR7 event_Y using the new source-specific variable-prefix uniform domination theorem 24aa95b9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_variable_prefix_C1_error_uniform_BV_dom
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_variable_prefix_event_C1_uniform_dom
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (a b L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      |w z - w y| ≤ L * |z - y|)
    (hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ L)
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
    (hCells : ∀ᵐ ω ∂P, ω ∈ s →
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℕ → ℝ := fun m i =>
         x + X.X (u m ω i) ω - rightLimit D (u m ω i) ω
       let c : ℕ → ℕ → ℝ := fun m i =>
         Y (u m ω (i + 1)) - Y (u m ω i)
       ∀ m i, i < k m ω →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b)) :
    ∀ᵐ ω ∂P, ∀ m,
      ‖if ω ∈ s then Err m ω else 0‖ ≤ (2 * L) * (|X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) := by sorry
