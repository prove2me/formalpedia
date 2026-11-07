-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_grid_event_local_uniform_BV_dom
-- name    : AvramDividend.Classical.avram_bv_error7_original_random_grid_event_local_uniform_BV_dom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:31:42.292707+00:00
-- url     : https://prove2.me/theorems/78d4d016-c30e-498f-bde7-8de339db9335
-- title:
--   Original BV source uniformly dominates event-localised sample-dependent physical C1 errors
-- statement:
--   For the authentic original BV Lévy process and admissible dividend, the source mass 2L(|drift|T+|T drift-X_T|) controls simultaneously every sample-dependent physical-grid Taylor residual on a given localisation event where the real stopped cell segments stay in a fixed compact positive-subcap band. Off the event the residual is zero, hence the same envelope dominates there automatically. The a.e. mass bound is established prior to selecting the sample-dependent grid, and no global compact path-band assumption, new law or signed BV prebudget is required.
-- source:
--   Exact event-localised consequence of the already Proved global all-grid physical Taylor source bound 12895109-9e0a-455c-b5af-3e5a94510b3b, with original X,D,J,Y unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_random_grid_event_local_uniform_BV_dom
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
    (hGrid : ∀ m ω, u m ω 0 = 0 ∧ u m ω (k m ω) = T ∧
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
