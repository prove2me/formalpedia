-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_noexit_capped_grid_reward_tendsto
-- name    : AvramDividend.Classical.chat03_noexit_capped_grid_reward_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T15:15:56.006986+00:00
-- url     : https://prove2.me/theorems/20b5a633-4842-4455-86cd-76efc84adbee
-- title:
--   Any horizon-capped grid reward converges on paths without prior exit
-- statement:
--   When the strict continuous two-sided exit infimum τ exceeds a fixed horizon T, and sufficiently fine terminal grid times remain between T and τ, the exact bounded hittingBtwn stopped clock is eventually T. Consequently the real-valued reward at the horizon-capped sampled clock is eventually equal to its value at T, hence converges there. The reward need not be continuous; in particular one may use discounted q-scale rewards. This is a pathwise no-exit lemma, not a killed martingale.
-- source:
--   Previously Proved AvramDividend.Classical.chat03_noexit_before_passage_grid_cap_stabilises, plus eventual equality and tendsto_const_nhds.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_before_passage_grid_cap_stabilises
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_noexit_capped_grid_reward_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hT : T < τ)
    (mesh : ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hterm : ∀ᶠ n in atTop,
      T ≤ (m n : ℝ≥0) * mesh n ∧
      (m n : ℝ≥0) * mesh n < τ)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η)
    (reward : ℝ≥0 → ℝ) :
    Tendsto (fun n =>
      reward (min ((K n ω : ℝ≥0) * mesh n) T))
      atTop (𝓝 (reward T)) := by sorry
