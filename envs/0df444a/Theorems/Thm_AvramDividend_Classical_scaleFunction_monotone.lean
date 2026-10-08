-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
-- name    : AvramDividend.Classical.scaleFunction_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T11:43:32.422671+00:00
-- url     : https://prove2.me/theorems/1c7655dc-6544-4dd0-9bcf-96acecffa075
-- title:
--   A q-scale function is globally monotone
-- statement:
--   The defining scale-function properties imply global monotonicity. On the negative half-line W is identically zero. Across zero, the negative value is zero while W is nonnegative on the positive half-line. For two nonnegative arguments, the MonotoneOn clause of IsScaleFunction applies. Consequently W is a globally monotone, hence Borel measurable, real function.
-- source:
--   Direct consequence of the support, nonnegativity and monotonicity clauses of IsScaleFunction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Monotone W := by sorry
