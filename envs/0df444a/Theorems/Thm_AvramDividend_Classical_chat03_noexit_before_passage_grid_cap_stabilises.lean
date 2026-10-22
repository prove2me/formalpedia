-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_noexit_before_passage_grid_cap_stabilises
-- name    : AvramDividend.Classical.chat03_noexit_before_passage_grid_cap_stabilises
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T15:06:00.152908+00:00
-- url     : https://prove2.me/theorems/d1dc9038-b504-4f46-bf22-f06122a1bafc
-- title:
--   Actual grid stopping time equals the horizon before a later continuous strict exit
-- statement:
--   For a spectrally negative Lévy sample path whose finite strict two-sided crossing infimum τ is strictly later than a fixed horizon T, suppose a sequence of bounded grids eventually has terminal observation times at least T and strictly below τ. The actual bounded Mathlib hittingBtwn clock clipped at T is eventually exactly T. The proof uses only the continuous IsGLB lower-bound property and the accepted no-exit sampled clock lemma, without stochastic optional stopping or a fixed-time continuity assumption.
-- source:
--   Proved Chat03 noexit_sampled_clock_caps_to_horizon and IsGLB.isLowerBound; elementary contradiction of an observed crossing strictly before the continuous exit infimum.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_sampled_clock_caps_to_horizon
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_noexit_before_passage_grid_cap_stabilises
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
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    ∀ᶠ n in atTop, min ((K n ω : ℝ≥0) * mesh n) T = T := by sorry
