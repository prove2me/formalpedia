-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fixed_terminal_esscher_strict_drawdown_infimum_reversal
-- name    : AvramDividend.Classical.avram_ws01e_b_fixed_terminal_esscher_strict_drawdown_infimum_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:47:23.55657+00:00
-- url     : https://prove2.me/theorems/92cd17c1-3ab5-46d7-978f-0098f06c398c
-- title:
--   Strict Lévy terminal drawdown and running-infimum reversal under genuine finite-terminal Esscher density
-- statement:
--   Under the genuine fixed-terminal compensated Esscher density exp(θ(X_T−X_0)−Tψ(θ)), the strict-event probability that the terminal Lévy drawdown is below a real threshold equals the strict-event probability that the running infimum relative to the initial value is below that threshold, for every deterministic positive finite horizon T. The proof applies the now-Proved Esscher-weighted terminal-increment finite-grid reversal to nested equal-mesh dyadic grids and passes to continuous time by path right-continuity and continuity from below. No global Esscher process, exponential observation clock, or Wiener–Hopf splitting is postulated.
-- source:
--   Proved actual_terminal_esscher_grid_reversal, strict_grid_path_probability_of_vector_reversal, right_continuous_strict_dyadic_grid_event, finite_dyadic_grid_refines.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_right_continuous_strict_dyadic_grid_event
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_finite_dyadic_grid_refines
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_terminal_esscher_grid_reversal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_grid_path_probability_of_vector_reversal

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_fixed_terminal_esscher_strict_drawdown_infimum_reversal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T)
    (θ a : ℝ) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (X.X T ω - X.X 0 ω) - (T : ℝ) * X.ψ θ)))
      {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧
        X.X T ω - X.X s ω < a}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (X.X T ω - X.X 0 ω) - (T : ℝ) * X.ψ θ)))
      {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧
        X.X s ω - X.X 0 ω < a}) := by sorry
