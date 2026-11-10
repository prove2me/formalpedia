-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_dense_observed_first_clock_eq_actual_negative_jump_inf
-- name    : AvramDividend.Classical.avram_bv_zero13_original_dense_observed_first_clock_eq_actual_negative_jump_inf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:46:27.567284+00:00
-- url     : https://prove2.me/theorems/265eb670-411e-4a0e-8709-fd7021221517
-- title:
--   Dense original negative cutoff count observation clock equals actual first physical negative jump time
-- statement:
--   For the actual spectrally negative Levy path and any countable dense deterministic sequence of observation clocks, the original countably observed physical negative cutoff jump detection clock is pathwise equal to the infimum over all genuine strictly negative jump times, with infinity when no such jump exists. Combines the Proved original physical cutoff positivity equivalence with real Archimedean cutoffs, density and order infimum inequalities. No artificial source process or extra filtration is used. This establishes the missing identification for the Proved observed-clock stopping interface; finite horizon clipping and D-specific zero reserve Stieltjes budget remain separate.
-- source:
--   Critical exact-clock identification required after 6b07c30d and f9d2039d, to use stopping-time laws 00cb3771 and 004fdd62 at the true first source negative jump.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_negative_band_count_real_positive_iff_exists_jump
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_dense_observed_first_clock_eq_actual_negative_jump_inf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℕ → ℝ≥0)
    (hr : ∀ u v : ℝ≥0, u < v → ∃ k : ℕ, u < r k ∧ r k < v)
    (ω : Ω) :
    let pastCount : ℕ → ℕ → Ω → ℝ :=
      fun n k ξ =>
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ξ -
            Function.leftLim (fun v : ℝ≥0 => X.X v ξ) u ≠ 0}).map
          (fun u : ℝ≥0 =>
            (u, X.X u ξ -
              Function.leftLim (fun v : ℝ≥0 => X.X v ξ) u)))
          (Ioc 0 (r k) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    (⨅ n : ℕ, ⨅ k : ℕ,
        if 0 < pastCount n k ω then (r k : WithTop ℝ≥0) else ⊤) =
      ⨅ u : ℝ≥0,
        if 0 < u ∧
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
        then (u : WithTop ℝ≥0) else ⊤ := by sorry
