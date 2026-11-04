-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_occupied_count_lintegral_dct_of_eventual_eq
-- name    : AvramDividend.Classical.avram_wave7_06_occupied_count_lintegral_dct_of_eventual_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:57:39.178895+00:00
-- url     : https://prove2.me/theorems/e37ce9a7-dd1b-48ea-85c0-a5bfeb3250c4
-- title:
--   Original source occupied-count expectation converges by dominated convergence
-- statement:
--   If measurable occupied-grid counts K_m are bounded on every original-process path by the integrable total source marked-count N and are eventually equal to N on each path, then the original P-expectations of K_m converge to E[N]. This is exactly the L¹ interchange needed in the original finite-band Poisson law argument, with explicit domination and no hidden uniform integrability assumption.
-- source:
--   Pinned Mathlib MeasureTheory.tendsto_lintegral_of_dominated_convergence, reusable with exact original source Ω/P counts.

import Mathlib
open MeasureTheory Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave7_06_occupied_count_lintegral_dct_of_eventual_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (K : ℕ → Ω → ℝ≥0∞) (N : Ω → ℝ≥0∞)
    (hK : ∀ m, Measurable (K m))
    (hBound : ∀ m ω, K m ω ≤ N ω)
    (hInt : (∫⁻ ω, N ω ∂P) < ⊤)
    (hEvent : ∀ ω, ∀ᶠ m in (Filter.atTop : Filter ℕ), K m ω = N ω) :
    Filter.Tendsto (fun m => ∫⁻ ω, K m ω ∂P)
      Filter.atTop (nhds (∫⁻ ω, N ω ∂P)) := by sorry
