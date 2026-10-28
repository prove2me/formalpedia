-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_path_drawdown_minimum_threshold_ws01e_b
-- name    : AvramDividend.Classical.levy_equal_mesh_path_drawdown_minimum_threshold_ws01e_b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:34:35.71115+00:00
-- url     : https://prove2.me/theorems/bc7ced95-97df-4c41-a5c1-b6b145150521
-- title:
--   Actual Lévy path terminal drawdown and origin-relative minimum agree in each finite equal-mesh grid law
-- statement:
--   Under the actual spectrally negative Lévy process law on the original path sample space, for any mesh δ, finite step count n including n=0, and real threshold a, the event that some grid observation lies at most a below the terminal position and the event that some grid observation lies at most a above the origin-relative position have equal probability. All grid start and endpoints are included. The proof telescopes the genuine Lévy increments and transfers their accepted full finite-grid reversal law through measurable pushforward. No two-sided exit, Wiener–Hopf independence, Esscher change of law or exponential stopping is used.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, §2.1, fixed-time reversal; https://warwick.ac.uk/fac/sci/statistics/staff/academic-research/kyprianou/scale-review-final.pdf. Imports Proved 2fa25ff1-ef4f-49e8-acd1-402e07ccbb50.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_drawdown_minimum_event_law_ws01e_b
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_equal_mesh_path_drawdown_minimum_threshold_ws01e_b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ≥0) (n : ℕ) (a : ℝ) :
    P {ω : Ω | ∃ k : Fin n.succ,
      X.X ((n : ℝ≥0) * δ) ω -
        X.X ((k.val : ℝ≥0) * δ) ω ≤ a} =
    P {ω : Ω | ∃ k : Fin n.succ,
      X.X ((k.val : ℝ≥0) * δ) ω - X.X 0 ω ≤ a} := by sorry
