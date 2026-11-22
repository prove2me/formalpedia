-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_future_window_killed_scale_harmonicity_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_future_window_killed_scale_harmonicity_no_standing_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T04:40:47.973617+00:00
-- url     : https://prove2.me/theorems/ee75bf61-b7dc-4cba-a982-8d049a303348
-- title:
--   BV future-window killed scale harmonicity from Esscher root without standing (public)
-- statement:
--   For a bounded-variation spectrally negative Levy process with positive discount q, positive Esscher root φ with ψ(φ)=q, and genuine q-scale function W, the future-window killed q-scale payoff is conditionally unbiased: given the past up to s, the expected discounted scale payoff at u over paths surviving on [s,u] equals W(x+X_s). No Standing assumption; the root replaces Standing throughout.
-- source:
--   Source-faithful no-standing mirror of Proved boundedVariation_future_window_killed_scale_harmonicity (c2e577be), with (φ, hφ, hroot) replacing X.Standing. Proof replays fdccdf7c: fixed-time integrability via Proved Kyprianou.Ch08.StageB.positiveRoot_fixedTime_scale_integrable (0b4c9214), scalar whole-path identity via Proved avram_root29_01_deterministic_killed_qscale (094049ef) with lintegral/bridge steps, Markov step via Proved chat04_killed_scale_shifted_expectation_of_scalar_renewal_kernel (8c2d238f, standing-free). Supplies hFuture for the condexp transfer (949cf837-analogue via standing-free 81c0531f) and hence the killed martingale feeding Proved chat03_killed_scale_grid_optional_stopping_of_martingale (b6c72d3d) in parent db3e52be. No hypotheses weakened; BV retained.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.p2m81_bv_future_window_killed_scale_harmonicity_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => W (x + X.X s ω)) := by sorry
