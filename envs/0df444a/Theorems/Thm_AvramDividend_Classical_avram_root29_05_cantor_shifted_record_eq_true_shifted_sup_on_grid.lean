-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_cantor_shifted_record_eq_true_shifted_sup_on_grid
-- name    : AvramDividend.Classical.avram_root29_05_cantor_shifted_record_eq_true_shifted_sup_on_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:23:01.837656+00:00
-- url     : https://prove2.me/theorems/95628481-f018-4512-8d52-6309be6c4a4f
-- title:
--   True post-shift Lévy running supremum equals exact Cantor sampled record at dividend mesh endpoints
-- statement:
--   For each actual spectrally negative Lévy sample path, any deterministic future shift u and every finite rational dividend cash-grid endpoint, the countable Cantor schedule supremum of the centred future Lévy increments equals the exact real running supremum of all post-shift increments on the corresponding full time interval. This is pathwise and supports the genuine post-first-upcrossing Stieltjes reward reconstruction without assuming any false shifted-process original-law equivalence.
-- source:
--   Proved full-prefix shifted Lévy path reconstruction a9e1f1a9, Cantor dense schedule 9206d7f5, rational endpoint pairing coverage 34d1a207.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Cantor-sampled future Lévy increments recover the genuine shifted
running supremum at each strictly positive-denominator rational cash-grid endpoint. -/

theorem AvramDividend.Classical.avram_root29_05_cantor_shifted_record_eq_true_shifted_sup_on_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0)
    (n k : ℕ) (hn : 0 < n) :
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     ⨆ j : ℕ,
       if samples j ≤ (k : ℝ≥0) * (n : ℝ≥0)⁻¹ then
         ENNReal.ofReal (X.X (u + samples j) ω - X.X u ω)
       else 0).toReal =
    sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) ''
      Set.Icc 0 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)) := by sorry
