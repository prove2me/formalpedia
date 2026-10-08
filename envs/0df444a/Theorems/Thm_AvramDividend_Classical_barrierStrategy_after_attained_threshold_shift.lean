-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_attained_threshold_shift
-- name    : AvramDividend.Classical.barrierStrategy_after_attained_threshold_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T07:19:20.361053+00:00
-- url     : https://prove2.me/theorems/453c4ed1-3388-49ad-a8df-82315d27479a
-- title:
--   Barrier dividends after an attained threshold are the reflected shifted-path supremum
-- statement:
--   Fix a path and times u,t. If the raw running supremum up to u is attained at X_u and X_u equals the barrier gap a−x, then cumulative barrier dividends by u+t equal the positive part of the supremum of the shifted future path r↦X_{u+r} above X_u on [0,t]. This is a deterministic restart identity at an attained barrier threshold and assumes no stopping-time or Markov property.
-- source:
--   Combination of the Prove2Me-Proved pointwise barrier offset, boundary-started running-supremum identity, raw-supremum representation, and runningSup_excess_after_peak theorem. It isolates the pathwise component of the strong-Markov barrier-value factorisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_after_attained_threshold_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (u t : ℝ≥0) (ω : Ω)
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t)))
    (hpeak : sSup ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u) = X.X u ω)
    (hlevel : X.X u ω = a - x) :
    barrierStrategy X x a (u + t) ω =
      max 0
        (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
          X.X u ω) := by sorry
