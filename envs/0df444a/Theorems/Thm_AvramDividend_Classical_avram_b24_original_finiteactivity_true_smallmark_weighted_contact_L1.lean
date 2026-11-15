-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_true_smallmark_weighted_contact_L1
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_true_smallmark_weighted_contact_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:29:04.398481+00:00
-- url     : https://prove2.me/theorems/235a7df8-6297-4fa1-af15-d282e7b07477
-- title:
--   True original finite-activity weighted compensated-mark ruin-contact residual vanishes in L1 under genuine endpoint gain integrability
-- statement:
--   For an arbitrary original intrinsic compensated smallmark source Jsmall of a true finite-negative-activity Lévy process X on its own Ω/P, let σ≤T be a true bounded physical terminal/ruin clock and finite physical last cells approach σ strictly from left and weakly from right, with uniformly bounded predictable coefficients W converging a.e. to a bounded left-contact weight. The error E_k is the actual weighted compensated smallmark last-cell increment minus the ACTUAL surviving small-negative Lévy marked atom at σ on σ>0, and zero on the σ=0 branch. Assuming only the natural integrability of each physical mesh error E_k, show the mean absolute error tends to zero. The proof uses the original smallmark all-time Poisson count plus drift L1 envelope, the original a.e. weighted true terminal marked jump limit, scalar bound 2LB+L and Proved dominated convergence. No large-jump moment or postruin path is used.
-- source:
--   Original B24 marked source uniform finite-activity Poisson-count L1 envelope, original weighted true terminal mark a.e., scalar 2LB+L bound, Proved DCT.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_true_smallmark_weighted_contact_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) (σ : Ω → ℝ≥0) (hσ : ∀ ω, σ ω ≤ T)
    (a b : ℕ → Ω → ℝ≥0)
    (hEndpoints : ∀ k ω, a k ω ≤ T ∧ b k ω ≤ T)
    (W : ℕ → Ω → ℝ) (Wleft : Ω → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hWBound : ∀ k ω, ‖W k ω‖ ≤ L)
    (hWleftBound : ∀ ω, ‖Wleft ω‖ ≤ L)
    (ha : ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => a k ω) atTop (𝓝[<] (σ ω)))
    (hb : ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => b k ω) atTop (𝓝[Ici (σ ω)] (σ ω)))
    (hW : ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => W k ω) atTop (𝓝 (Wleft ω)))
    (E : ℕ → Ω → ℝ)
    (hE : ∀ k ω, E k ω =
      if 0 < σ ω then
        W k ω * (Jsmall (b k ω) ω - Jsmall (a k ω) ω) -
        Wleft ω *
          (if -1 < X.X (σ ω) ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω) ∧
               X.X (σ ω) ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω) < 0
           then X.X (σ ω) ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω)
           else 0) else 0)
    (hEI : ∀ k, Integrable (E k) P) :
    Tendsto (fun k => ∫ ω, ‖E k ω‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
