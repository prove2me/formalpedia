-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_limsup_reward_eq_true_drawdown
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_shifted_levy_limsup_reward_eq_true_drawdown
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T20:12:45.992996+00:00
-- url     : https://prove2.me/theorems/91c5d4c8-6fa0-41b6-a6e5-ed1840c53c8e
-- title:
--   Actual shifted Lévy drawdown exponential equals the measurable dyadic Cantor limsup reward pathwise
-- statement:
--   For the genuine spectrally negative Lévy process, any path ω, any base u and future duration t, and any real β, the ENNReal limsup of the explicit dyadic-ceiling countably sampled exponential of the centred shifted-path drawdown equals exactly exp(−β D), with D the true raw supremum of centred post-u increments minus its terminal increment. It is a pathwise equality at all ω,u,t, without stochastic exceptional sets. Combined with the separately published unrestricted-product-Pi measurability of the same limsup, this lets the proved genuine Qp record regeneration theorem act on the exact terminal drawdown functional.
-- source:
--   The accepted source-specific shifted Cantor dyadic drawdown convergence theorem (submitted independently after its shifted prefix predecessor); pinned Mathlib Filter.Tendsto.limsup_eq and Filter.limsup_eq_iInf_iSup_of_nat; uncapped Qp regeneration 4cf7269f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_shifted_levy_limsup_reward_eq_true_drawdown
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u t : ℝ≥0) (β : ℝ) :
    (⨅ k : ℕ, ⨆ n : ℕ, if k ≤ n then
        let r : ℝ≥0 :=
          (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
        let samples : ℕ → ℝ≥0 := fun j =>
          ((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
        ENNReal.ofReal (Real.exp
          (-β * ((⨆ i : ℕ, if samples i ≤ r then
            ENNReal.ofReal (X.X (u + samples i) ω - X.X u ω) else 0).toReal -
              (X.X (u + r) ω - X.X u ω))))
      else 0) =
    ENNReal.ofReal (Real.exp (-β *
      (sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
        (X.X (u + t) ω - X.X u ω)))) := by sorry
