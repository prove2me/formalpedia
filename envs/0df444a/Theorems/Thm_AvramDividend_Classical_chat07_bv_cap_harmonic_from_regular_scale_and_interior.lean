-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_cap_harmonic_from_regular_scale_and_interior
-- name    : AvramDividend.Classical.chat07_bv_cap_harmonic_from_regular_scale_and_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:11:34.630015+00:00
-- url     : https://prove2.me/theorems/3c02ea3c-01a7-47c6-a564-b1a70894b287
-- title:
--   Bounded-variation exact cap generator harmonicity from scale regularity and interior identity
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process with vanishing Gaussian coefficient, and a positive canonical barrier where the scale derivative is nonzero, assume positive-axis C1 and C2 regularity of the scale function and exact q-harmonicity strictly inside the barrier. Then the complete nonlocal generator of the dividend-value candidate exists at the barrier and is exactly q-harmonic there. The generator-domain property follows from accepted BV C1 integrability, the residual continuity follows from accepted BV C2 theory, and the first boundary jet is supplied by accepted smooth fit. This isolates interior scale-function harmonicity as the substantive remaining assumption in the regular BV branch.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_bv_cap_harmonic_from_regular_scale_and_interior
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (hσ : X.σ = 0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ha : 0 < (cstar W).toReal)
    (hWdiff : DifferentiableAt ℝ W (cstar W).toReal)
    (hWderiv : deriv W (cstar W).toReal ≠ 0)
    (hC1 : ContDiffOn ℝ 1 W (Ioi 0))
    (hC2 : ContDiffOn ℝ 2 W (Ioi 0))
    (hinside : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by sorry
