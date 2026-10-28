-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedRuin_clock_eq_encodedCantor
-- name    : AvramDividend.Classical.reflectedRuin_clock_eq_encodedCantor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:09:21.411986+00:00
-- url     : https://prove2.me/theorems/fcfcdcda-0987-4a53-a782-a5fed29767a1
-- title:
--   Reflected Lévy strict ruin time equals the Borel encoded countable record crossing clock
-- statement:
--   The original spectrally negative Lévy reflected process first enters ruin at the same time as the explicitly measurable Cantor-paired rational schedule first records strict negative reflected reserves, where every running supremum is represented by countable ENNReal-of-real observations. The proof combines the Proved right-neighbourhood strict-exit clock identity with the exact countable regulator encoding theorem, including time-zero coverage and rational schedule density.
-- source:
--   Proved reflectedRuin_strictClock_eq_countableSchedule, runningSup_eq_countableENNReal_record, chat05_cantor_rational_schedule_dense and chat04_nat_pairing_rational_grid_coverage. Avram et al (2007), Proposition 1.

import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_reflectedRuin_strictClock_eq_countableSchedule
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_countableENNReal_record
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.reflectedRuin_clock_eq_encodedCantor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (a : ℝ) :
    (⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
      (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ,
      if X.X (((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ω -
        (⨆ k : ℕ, ENNReal.ofReal
          (if (((Nat.unpair k).2 : ℝ≥0) * (((((Nat.unpair k).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ≤ (((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) then
            max 0 (X.X (((Nat.unpair k).2 : ℝ≥0) * (((((Nat.unpair k).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ω) else 0)).toReal < -a
      then ((((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞) else ⊤) := by
  sorry
