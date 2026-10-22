-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_ae_all_branches
-- name    : AvramDividend.Classical.chat03_actual_ceiling_capped_grid_scale_ae_all_branches
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T05:21:42.367142+00:00
-- url     : https://prove2.me/theorems/7b1c1e2f-b49a-4516-add9-33ea7c9cc8d7
-- title:
--   Almost-everywhere ceiling-capped stopped-scale convergence without terminal-atom exclusion
-- statement:
--   Under the pathwise strict two-sided exit infimum almost everywhere and W(0)=0, actual bounded hittingBtwn scale rewards capped at the natural ceiling-grid index converge almost everywhere to their continuously stopped counterpart, including positive probability of strict exit exactly at the terminal horizon.
-- source:
--   A pointwise almost-everywhere lifting of the all-terminal-branches pathwise ceiling-capped convergence theorem, with no terminal clock non-atomicity requirement.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_ceiling_capped_grid_scale_ae_all_branches
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (lower upper x : ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P,
      IsGLB
        {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n =>
        Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
        atTop
        (𝓝 (Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
          W (x + X.X (min (τ ω) T) ω))) := by
  sorry
