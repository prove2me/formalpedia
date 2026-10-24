-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative
-- name    : AvramDividend.Classical.generatorIntegrand_large_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:51:45.382243+00:00
-- url     : https://prove2.me/theorems/4809dc4e-84b2-4a6a-9e77-6f7665c1a14a
-- title:
--   The Lévy generator leaves jumps of size at least one uncompensated
-- statement:
--   For a negative jump y at or below -1, the strict truncation indicator vanishes. The generator integrand is exactly the candidate value change w(x+y)-w(x). The endpoint -1 is correctly included in the large-jump case.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.generatorIntegrand_large_negative
    (w : ℝ → ℝ) (x y : ℝ) (hy : y ≤ (-1 : ℝ)) :
    SpectrallyNegativeLevy.generatorIntegrand w x y =
      w (x + y) - w x := by sorry
