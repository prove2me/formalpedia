-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_generator_above_eq_drift_add_jump
-- name    : AvramDividend.Classical.vcstar_generator_above_eq_drift_add_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T07:47:44.819379+00:00
-- url     : https://prove2.me/theorems/acee133e-3423-4e68-a1b6-832c095dcd8b
-- title:
--   Exact above-cap Lévy generator: drift plus the nonlocal compensated jump integral
-- statement:
--   For a spectrally negative Lévy process X and the exact dividend-barrier value candidate vcstar W, at any reserve x above the formal real cap, the Lévy generator equals the drift coefficient X.c plus the actual compensated negative-jump integral. Both the Gaussian second-order term and the nonunit derivative factor simplify away by the strict-right affine geometry. The jump integral is retained exactly rather than replaced by a globally affine expression, avoiding illegitimate separation under heavy-tailed negative jumps.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_generator_above_eq_drift_add_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (x : ℝ)
    (hx : (cstar W).toReal < x) :
    X.generator (vcstar W) x =
      X.c + ∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν := by sorry
