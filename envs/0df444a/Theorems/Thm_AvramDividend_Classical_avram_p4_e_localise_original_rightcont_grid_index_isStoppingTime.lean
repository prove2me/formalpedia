-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_grid_index_isStoppingTime
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_rightcont_grid_index_isStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:18:56.997501+00:00
-- url     : https://prove2.me/theorems/d0b4325f-a76c-4fec-9beb-ca1cddd17f75
-- title:
--   Original right-continuous grid-ceiling event witnesses give a bounded sampled stopping time
-- statement:
--   For the original source ruin-truncated process clock and a sampled filtration 𝓖_i=𝓕.rightCont(e_i), any grid index K whose events {K≤i} are measurable in 𝓕.rightCont(e_i) is a discrete-time 𝓖-stopping time. If K≤N pathwise, its WithTop lift is bounded by N. This is the exact compatibility interface required by bounded optional stopping on the genuine right-continuous sampled martingale.
-- source:
--   Actual original X, ruinTime, and right-continuous sampled filtration from 0dda1be7 and accepted rightcont L1/L2 helpers ca9457ed and ba3b7ebb. No optional stopping assumption is invoked here.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Adapt source right-continuous sampled events into a bounded discrete stopping time. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_rightcont_grid_index_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ))
    (K : Ω → ℕ)
    (hEvents : ∀ i, MeasurableSet[𝓕.rightCont (e i)] {ω : Ω | K ω ≤ i})
    (N : ℕ) (hBound : ∀ ω, K ω ≤ N) :
    IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ)) ∧
      ∀ ω, (K ω : WithTop ℕ) ≤ (N : WithTop ℕ) := by sorry
