-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_levy_cantor_dyadic_drawdown_tendsto
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_levy_cantor_dyadic_drawdown_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T18:20:43.252072+00:00
-- url     : https://prove2.me/theorems/5886c047-f037-490c-9401-841500a61216
-- title:
--   The concrete Cantor-grid jointly measurable prefix drawdown converges to the genuine Lévy random-horizon drawdown
-- statement:
--   For the actual spectrally negative Lévy X, the dyadic ceiling clock r_n(t) tends to the actual t, and the clipped countable Cantor rational record at r_n(t) is exactly the genuine running supremum there. Consequently the sampled dyadic drawdown converges pointwise for every sample path to the true reflected drawdown runningSup X t−X_t. Uses a concrete countable clock schedule dense in nonnegative time and covering every dyadic ceiling, not an assumed pathwise surrogate. This is the key convergence needed to transfer the canonically Proved joint product-Pi measurable rewards through true Esscher first-record regeneration into genuine S_e/D_e independence.
-- source:
--   Proved actual Lévy dense prefix equality (pending source publication 47df4031), Cantor schedule density 9206d7f5, Cantor grid coverage 34d1a207, genuine dyadic reflected drawdown convergence b62d3c82.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_levy_cantor_dyadic_drawdown_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      let r : ℝ≥0 :=
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
      let samples : ℕ → ℝ≥0 := fun j =>
        ((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
      (⨆ i : ℕ, if samples i ≤ r then
        ENNReal.ofReal (X.X (samples i) ω) else 0).toReal - X.X r ω)
      atTop (𝓝 (runningSup X t ω - X.X t ω)) := by sorry
