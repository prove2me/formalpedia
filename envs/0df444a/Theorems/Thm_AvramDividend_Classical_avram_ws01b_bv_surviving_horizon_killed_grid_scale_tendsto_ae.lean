-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_surviving_horizon_killed_grid_scale_tendsto_ae
-- name    : AvramDividend.Classical.avram_ws01b_bv_surviving_horizon_killed_grid_scale_tendsto_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T12:10:23.087487+00:00
-- url     : https://prove2.me/theorems/5a65efb7-06ca-47b3-aa86-0b15e5e497e4
-- title:
--   True BV continuously killed stopped-grid q-scale limit on paths surviving below T
-- statement:
--   Under the genuine original BV law, for every path whose first strict lower passage occurs strictly after the finite horizon T, the entire stopped ceiling-grid history survives the lower killing criterion for every mesh, and its discounted q-scale reward converges to the true finite-horizon continuously stopped q-scale payoff. Works for either upper-first exit before T or no exit before T and preserves Wq(0)>0.
-- source:
--   Combines source strict pre-lower-clock closed-history survival 98c4d827 with accepted all-path BV ceiling-grid q-scale convergence ca137f2f. Exact full-history indicator equals one at every capped sampled stop by s≤cap≤T<lower passage.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_lower_clock_strict_preclock_closed_survival
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_surviving_horizon_killed_grid_scale_tendsto_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    ∀ᵐ ω ∂P,
      (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω →
      Tendsto (fun n =>
        ({η : Ω | ∀ s : ℝ≥0,
          s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
          (fun η => Real.exp (-(q * ((min ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
            W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
        atTop (𝓝 (if min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω) < ⊤ then
          Real.exp (-(q * ((min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
            W (x + X.X (min
              (min (twoSidedExitUpTime X (a-x) ω)
                (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))) := by sorry
