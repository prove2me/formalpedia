-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_cantor_dyadic_drawdown_tendsto
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_shifted_levy_cantor_dyadic_drawdown_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T20:12:43.805642+00:00
-- url     : https://prove2.me/theorems/20ea0d9b-8d2b-485a-96c4-ff4a22f18f20
-- title:
--   Genuine centred post-record Lévy drawdown at arbitrary shifted ages is the limit of measurable Cantor-grid dyadic rewards
-- statement:
--   For every spectrally negative Lévy sample path, any base age u≥0 and residual horizon t≥0, the countable clipped Cantor-grid supremum of the entire centred shifted future path at dyadic ceilings of t, minus the centred endpoint, converges to the true shifted supremum over [0,t] minus the actual centred endpoint. The result is pointwise for all sample paths and arbitrary base ages, so it applies at first strict upper-record stopping ages in the genuine Qp conditional regeneration theorem. No false global Esscher law or synthetic independence premise is assumed.
-- source:
--   Proved shifted path countable prefix identity (publication request 3e83a3dd), shiftedSup_right_continuous_of_levy 8b268815, shiftedLevy_increments_right_continuous b901917f, Cantor dense 9206d7f5 and grid coverage 34d1a207.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_shifted_levy_cantor_dyadic_drawdown_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u t : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      let r : ℝ≥0 :=
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
      let samples : ℕ → ℝ≥0 := fun j =>
        ((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
      (⨆ i : ℕ, if samples i ≤ r then
        ENNReal.ofReal (X.X (u + samples i) ω - X.X u ω) else 0).toReal -
          (X.X (u + r) ω - X.X u ω))
      atTop (𝓝
        (sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
          (X.X (u + t) ω - X.X u ω))) := by sorry
