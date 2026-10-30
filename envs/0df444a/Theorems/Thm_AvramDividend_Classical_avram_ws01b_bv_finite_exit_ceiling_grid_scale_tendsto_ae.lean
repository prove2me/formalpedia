-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_finite_exit_ceiling_grid_scale_tendsto_ae
-- name    : AvramDividend.Classical.avram_ws01b_bv_finite_exit_ceiling_grid_scale_tendsto_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:31:55.835795+00:00
-- url     : https://prove2.me/theorems/a2e4297c-12b0-4ee9-b886-e9a01b115dd4
-- title:
--   Original BV finite strict two-sided exit ceiling-grid q-scale converges a.e.
-- statement:
--   For original Standing BV Levy paths starting between zero and positive a, genuine ceiling-capped strict two-sided first-grid discounted q-scale payoffs converge almost surely on every trajectory with finite first exit. The finite named exit clocks are identified with the pathwise strict-exit infimum, and the q-scale is continuous at the actual stopped reserve almost surely. This resolves the early-exit component of the BV continuous-time optional-stopping limit, without Wq(0)=0.
-- source:
--   Combines Proved original BV stochastic finite-stopped-reserve continuity 941a3a0b, exact finite official two-sided clock IsGLB bb38e95f and genuine all-branches ceiling-grid pathwise convergence of local continuity (new dependency). No assumption of global origin continuity or finite jump activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_stopped_scale_continuity_ae
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_finite_two_sided_min_isGLB
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_ceiling_capped_grid_scale_tendsto_of_continuity

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_finite_exit_ceiling_grid_scale_tendsto_ae
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
      min (twoSidedExitUpTime X (a-x) ω)
        (twoSidedExitDownTime X (-x) ω) < ⊤ →
      Tendsto (fun n =>
        Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
        atTop
        (𝓝 (Real.exp (-(q * ((min
          (min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω))) := by sorry
