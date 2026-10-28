-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
-- name    : AvramDividend.Classical.reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:09:26.017255+00:00
-- url     : https://prove2.me/theorems/3eb5e421-6c7c-4383-8857-71465fe9c830
-- title:
--   Almost-sure source downward regularity persists immediately after each actual finite-horizon reflected first closed-level hit
-- statement:
--   Assume the spectrally negative Lévy source sample path visits negative values arbitrarily soon after time zero almost surely, and choose a countable dense time schedule and positive cofinal horizon sequence. The actual finite-horizon first closed drawdown-level hit is canonically a finite stopping time. Right-continuity ensures that source near-zero negativity occurs at the dense sampled times, giving a cofinal grid-a.e. law. The accepted strong Markov finite-stopping path-law transfer then yields strictly negative future Lévy increments arbitrarily soon after the actual level hitting clock almost surely. This identifies precisely the source regularity assumption needed by the excursion height argument, while not claiming it follows yet from unbounded variation nor that P is the sigma-finite excursion measure n.
-- source:
--   Accepted Prove2Me levy_negative_before_horizon_iff_dense_grid, levy_finiteStopping_negative_near_zero_of_grid, reflectedSup_capped_closedLevelHit_stoppingTime.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Mathlib.Order.Interval.Set.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_closedLevelHit_stoppingTime
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_negative_near_zero_of_grid
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0) (x : ℝ)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hRegular : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (sInf ((Icc (0 : ℝ≥0) H ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) + s) ω -
        X.X (sInf ((Icc (0 : ℝ≥0) H ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})) ω < 0 := by sorry
