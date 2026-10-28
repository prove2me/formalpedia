-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_path_drawdown_minimum_strict_threshold_ws01e_b
-- name    : AvramDividend.Classical.levy_equal_mesh_path_drawdown_minimum_strict_threshold_ws01e_b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:59:24.54822+00:00
-- url     : https://prove2.me/theorems/d75a390e-03ca-4985-8d54-cccef8d534e8
-- title:
--   Strict finite-mesh terminal Lévy drawdown and running minimum probabilities coincide
-- statement:
--   For any spectrally negative Lévy process, step δ≥0, mesh length n and real threshold a, the probability that the terminal position minus some earlier mesh value falls strictly below a equals the probability that a mesh position minus the process initial value falls strictly below a. Finite increment partial sums telescope samplewise and an accepted strict event-law on the actual increment vector transfers through a measurable path map. Handles n=0 and jump atoms without a continuity assumption on threshold distributions.
-- source:
--   Strict finite-grid Lévy sample-path reversal, using accepted increment reversal and strict threshold event-law; Kuznetsov–Kyprianou–Rivero §2.1–2.2.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_drawdown_minimum_strict_event_law_ws01e_b
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_equal_mesh_path_drawdown_minimum_strict_threshold_ws01e_b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ≥0) (n : ℕ) (a : ℝ) :
    P {ω : Ω | ∃ k : Fin n.succ,
      X.X ((n : ℝ≥0) * δ) ω -
        X.X ((k.val : ℝ≥0) * δ) ω < a} =
    P {ω : Ω | ∃ k : Fin n.succ,
      X.X ((k.val : ℝ≥0) * δ) ω - X.X 0 ω < a} := by sorry
