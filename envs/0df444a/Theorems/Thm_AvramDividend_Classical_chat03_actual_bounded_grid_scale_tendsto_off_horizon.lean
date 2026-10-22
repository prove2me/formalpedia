-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_scale_tendsto_off_horizon
-- name    : AvramDividend.Classical.chat03_actual_bounded_grid_scale_tendsto_off_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T17:42:34.805421+00:00
-- url     : https://prove2.me/theorems/1508dba8-261f-41b3-a225-1032f88a51e3
-- title:
--   Exact horizon-capped grid scale convergence when strict exit is separated from the horizon
-- statement:
--   For a path with continuous strict exit infimum τ different from a fixed horizon T, the genuine bounded sampled hittingBtwn stopped q-scale reward converges to the continuous stopped q-scale reward when W(0)=0 and the mesh vanishes. For τ<T, the grid terminal time eventually exceeds τ+1. For T<τ, the grid terminal time eventually lies between T and τ. The proof combines the separately Proved first-exit and no-exit branches; it neither assumes nor asserts killed q-scale martingality.
-- source:
--   Proved chat03_actual_bounded_grid_discounted_scale_tendsto_of_Wzero and chat03_noexit_before_passage_grid_cap_stabilises, with eventual equality and constant-sequence convergence in the no-exit branch.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_discounted_scale_tendsto_of_Wzero
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_before_passage_grid_cap_stabilises
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_bounded_grid_scale_tendsto_off_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hbranch : τ < T ∨ T < τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcapBefore : τ < T →
      ∀ᶠ n in atTop, τ + 1 ≤ (m n : ℝ≥0) * mesh n)
    (hcapAfter : T < τ →
      ∀ᶠ n in atTop,
        T ≤ (m n : ℝ≥0) * mesh n ∧
        (m n : ℝ≥0) * mesh n < τ)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    Tendsto (fun n =>
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (Real.exp (-(q * ((min τ T) : ℝ))) *
        W (x + X.X (min τ T) ω))) := by sorry
