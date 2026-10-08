-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_shift_ae_continuous_of_standing_bv
-- name    : AvramDividend.Classical.scaleFunction_shift_ae_continuous_of_standing_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:24:52.035993+00:00
-- url     : https://prove2.me/theorems/7a3c0ab9-9872-4aaa-81c0-1281db10cf05
-- title:
--   Shifted scale function is almost everywhere continuous for bounded-variation Lévy jumps
-- statement:
--   For a bounded-variation spectrally negative Lévy process under the paper's standing assumptions, the Lévy measure is atomless. At any positive state x the q-scale function W is continuous at x+y for almost every negative jump y, because W is continuous away from its possibly discontinuous origin and only the singleton y=-x can hit the origin. This is the precise measure-theoretic input needed for almost-everywhere state continuity of the compensated generator in the bounded-variation branch.
-- source:
--   The accepted standing bounded-variation Lévy atomlessness and q-scale continuity-away-origin theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_shift_ae_continuous_of_standing_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    ∀ᵐ y ∂(X.ν.restrict (Iio 0)), ContinuousAt W (x + y) := by sorry

end AvramDividend.Classical
