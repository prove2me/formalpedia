-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_limsup_reward_measurable_fresh_shifted
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_limsup_reward_measurable_fresh_shifted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:48:30.850147+00:00
-- url     : https://prove2.me/theorems/ce317107-21be-4851-b81b-fc4ce1728dd0
-- title:
--   Measurable Pi-path limsup drawdown reward with actual fresh and shifted Lévy path identities
-- statement:
--   The dyadic-ceiling and dense rational-prefix approximation to exponentiated terminal drawdown defines a jointly measurable nonnegative function H of the residual duration and an arbitrary Pi-path. At every actual spectrally negative Lévy sample path, H at the fresh horizon equals the genuine running-supremum drawdown Laplace reward; H at a shifted path equals the exact shifted supremum minus terminal increment reward. These conclusions follow from the accepted sampled-reward measurability, unshifted drawdown convergence and shifted limsup identity, without supposing that variable-time evaluation of an arbitrary Pi-path is measurable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_dyadic_ceiling_prefix_drawdown_reward_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_levy_cantor_dyadic_drawdown_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_limsup_reward_eq_true_drawdown
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_limsup_reward_measurable_fresh_shifted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (β : ℝ) :
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun t f =>
       Filter.limsup (fun n : ℕ =>
         let r : ℝ≥0 :=
           (Nat.ceil ((t : ℝ) * (2 : ℝ)^n) : ℝ≥0) / (2 : ℝ≥0)^n
         ENNReal.ofReal (Real.exp
           (-β * ((⨆ i : ℕ, if samples i ≤ r then
             ENNReal.ofReal (f (samples i)) else 0).toReal - f r)))) Filter.atTop
     Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2) ∧
     (∀ (ω : Ω) (t : ℝ≥0),
       H t (fun s : ℝ≥0 => X.X s ω) =
         ENNReal.ofReal (Real.exp (-β * (runningSup X t ω - X.X t ω)))) ∧
     (∀ (ω : Ω) (u t : ℝ≥0),
       H t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω) =
         ENNReal.ofReal (Real.exp (-β *
           (sSup ((fun v : ℝ≥0 =>
             X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
             (X.X (u + t) ω - X.X u ω)))))) := by sorry
