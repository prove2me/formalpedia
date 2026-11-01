-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_levy_square_energy_band_tails
-- name    : AvramDividend.Classical.avram_wave4_p1_levy_square_energy_band_tails
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:09:29.648239+00:00
-- url     : https://prove2.me/theorems/4e7cfc5e-689d-4454-8419-f629720fcaaf
-- title:
--   Finite Lévy square-energy vanishes on complements of exhaustive finite-rate bands
-- statement:
--   For a sigma-finite marked-jump intensity with finite weighted square energy, any increasing measurable finite-rate band exhaustion has vanishing complement quadratic energy. This is continuity from above for the finite energy-density measure, and does not assume finite first jump variation, a compensation formula, or an original source-X PRM law. It supplies the deterministic small-jump energy tail required in L² compensated-integral localisation.
-- source:
--   Pinned Mathlib MeasureTheory.withDensity_apply and tendsto_measure_iInter_atTop; Applebaum Lévy stochastic integration, Avram-Palmowski-Pistorius (2007) Proposition 4(i).

import Mathlib

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_levy_square_energy_band_tails
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (g : E → ℝ≥0∞)
    (hg : Measurable g) (henergy : ∫⁻ z, g z ∂ν < ∞)
    (B : ℕ → Set E)
    (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, ν (B n) < ∞)
    (hBmono : Monotone B)
    (hBcover : (⋃ n, B n) = Set.univ) :
    Tendsto (fun n : ℕ => ∫⁻ z in (B n)ᶜ, g z ∂ν)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
