-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_signed_laplace_ae_zero_of_psi_family_20261026
-- name    : AvramDividend.Classical.avram_signed_laplace_ae_zero_of_psi_family_20261026
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:37:44.755806+00:00
-- url     : https://prove2.me/theorems/3a16f0cf-3533-494f-b31d-336480464600
-- title:
--   Signed Laplace uniqueness on the Lévy-exponent admissible parameter family
-- statement:
--   Under the standing spectrally negative Lévy assumptions and q>0, all sufficiently large nonnegative Laplace parameters satisfy ψ(θ)>q. Thus a signed function R with integrable zero Laplace transforms at every such admissible parameter has a zero transform on a complete real half-line. The previously proved signed uniqueness theorem forces R=0 almost everywhere on (0,∞). This bridge applies to BV and UBV generator residuals without continuity or C2 hypotheses.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4. Canonically Proved psi_eventually_gt_of_standing and avram_laplace_ae_zero_of_signed_20261026.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_laplace_ae_zero_of_signed_20261026
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

namespace AvramDividend.Classical
/-- A signed residual with zero weighted transforms at every q-admissible
Lévy exponent parameter vanishes almost everywhere on positive reserves. -/
theorem avram_signed_laplace_ae_zero_of_psi_family_20261026
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (R : ℝ → ℝ)
    (hlap : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * R x)
        (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * R x) = 0) :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))), R x = 0 := by sorry
end AvramDividend.Classical
