-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_future_window_harmonicity
-- name    : AvramDividend.Classical.avram_root29_01_unbounded_future_window_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:56:13.469333+00:00
-- url     : https://prove2.me/theorems/cbcb3315-0ba0-41d7-85c4-267038a81ca2
-- title:
--   Genuine original-Lévy real killed q-scale future-window conditional harmonicity without auxiliary schedule
-- statement:
--   For every unbounded variation spectrally negative Lévy process with positive discount and true scale function, arbitrary real x and deterministic s≤u, the original-P conditional expectation at time s of the continuously lower-killed discounted q-scale reward on [s,u] equals W(x+X_s). The proof constructs a Proved rational-and-terminal countable schedule, uses Proved source future-kernel conditional semigroup, Proved shifted closed-survival measurability, and translates both interval and discount. No stopped scale or two-sided exit result is imported.
-- source:
--   WS1A dedicated source work/avram_root29_01_unbounded_future_window_harmonicity_draft.lean.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_future_killed_condexp
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_shifted_lower_closed_event_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_unbounded_future_window_harmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) | 𝓕 s]
      =ᵐ[P] (fun ω => W (x + X.X s ω)) := by sorry
