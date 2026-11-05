-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_signed_GH_ae_sign_closed_under_clock_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_signed_GH_ae_sign_closed_under_clock_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:34:20.94825+00:00
-- url     : https://prove2.me/theorems/545fc83c-2fc6-40b6-a63a-bdf4f1a7f0b6
-- title:
--   Nonpositive original signed G+H residual survives almost-sure stopped clock limiting passage
-- statement:
--   For the exact original ruin-clipped stopped clock, if finite-grid generator/drift residuals Gk and dividend residuals Hk converge almost surely separately to G,H, and all finite-stage sums are nonpositive on a single conull event, then the exact stopped limit G+H remains nonpositive almost surely. This is a rigorous closed-inequality limit interface, and requires the actual source finite-stage sign and convergence data.
-- source:
--   Pinned Mathlib tendsto of sums and closed order interval Iic 0; original P4-F residual terms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped signed generator/dividend residual envelope remains nonpositive at an a.e. clock limit. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_signed_GH_ae_sign_closed_under_clock_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (Gk Hk : ℕ → Ω → ℝ) (G H : Ω → ℝ)
    (hG : ∀ᵐ ω ∂P,
      Tendsto (fun k => Gk k ω) atTop (𝓝 (G ω)))
    (hH : ∀ᵐ ω ∂P,
      Tendsto (fun k => Hk k ω) atTop (𝓝 (H ω)))
    (hSign : ∀ᵐ ω ∂P,
      ∀ k, Gk k ω + Hk k ω ≤ 0) :
    ∀ᵐ ω ∂P, G ω + H ω ≤ 0 := by sorry
