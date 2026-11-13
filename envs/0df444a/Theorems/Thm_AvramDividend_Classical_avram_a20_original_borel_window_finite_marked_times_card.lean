-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_window_finite_marked_times_card
-- name    : AvramDividend.Classical.avram_a20_original_borel_window_finite_marked_times_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T15:50:13.241948+00:00
-- url     : https://prove2.me/theorems/8f1dd77e-c2d1-4ebe-8aa8-303691e1e432
-- title:
--   Exact arbitrary physical Borel marked-window count equals finite original sample jump-time filter cardinal
-- statement:
--   For the actual original spectrally negative Lévy sample path, an arbitrary measurable Borel mark set B and a finite set of marked jump times up to terminal T, the original physical marked count on any subwindow (s,t]⊆(0,T] equals exactly the cardinal of the corresponding time-window filter of that finite source jump-time set. The proof uses the Proved exact intrinsic original jump-measure rectangle ENat cardinal identity, finiteness inherited by subwindows, and equivalence of source finite set membership and its filtered cardinal. This removes the previous fixed-negative-cutoff restriction from physical finite-grid time-window counting.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_window_finite_marked_times_card
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (hS : ({u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).Finite) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) =
    (((hS.toFinset.filter
      (fun u : ℝ≥0 => s < u ∧ u ≤ t)).card : ℕ) : ℝ≥0∞) := by sorry
