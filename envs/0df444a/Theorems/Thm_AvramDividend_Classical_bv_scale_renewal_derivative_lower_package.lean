-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scale_renewal_derivative_lower_package
-- name    : AvramDividend.Classical.bv_scale_renewal_derivative_lower_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:18:15.851124+00:00
-- url     : https://prove2.me/theorems/90d38fd3-f82e-4194-9807-4db778adea5a
-- title:
--   BV scale renewal derivative with positive jump-tail and convolution remainder
-- statement:
--   Identify the bounded-variation q-scale function at the origin as 1/d, and express its positive-axis ordinary derivative via a differentiated renewal equation. The jump-tail contribution is W(0) times the rate of negative jumps larger than the reserve x, with a nonnegative convolution residual. The identity follows from the Lévy Laplace exponent and the source IsScaleFunction transform. Its positive terms imply W'(x)≥ν(-∞,-x)/d² and therefore close the infinite-activity zero-barrier scale-slope leaf in conjunction with the already-Proved continuous-cutoff jump tail divergence. The finite-activity branch additionally needs to show the residual tends to zero at the origin.
-- source:
--   Kuznetsov–Kyprianou–Rivero scale-function review, bounded-variation renewal identity and its derivative; Avram–Palmowski–Pistorius (2007) §3.3. Exact hX Standing supplies positive drift and absolute continuity of ν.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_scale_renewal_derivative_lower_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) :
    W 0 = 1 / X.drift ∧
      ∀ x : ℝ, 0 < x → ∃ R : ℝ,
        0 ≤ R ∧
          X.drift * deriv W x =
            q * W x + (X.ν (Iio (-x))).toReal * W 0 + R := by sorry
