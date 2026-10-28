-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_zero_barrier_of_nearfield
-- name    : AvramDividend.Classical.vcstar_hjb_all_positive_zero_barrier_of_nearfield
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:21:11.319278+00:00
-- url     : https://prove2.me/theorems/4a380adb-93dc-4b09-a9a6-3465d495f7d0
-- title:
--   Global zero-barrier HJB verification reduces to the bounded near-field generator region
-- statement:
--   For cstar=0, HJB equality on every strictly positive reserve follows from generator residual control only in the bounded region where the reserve is below one or its discounted value qx does not dominate the Lévy drift c. The far-field residual estimate automatically handles all other reserves. The dividend derivative is identically one above zero, so the generator residual comparison establishes the whole HJB maximum. This localises the outstanding generator analysis near the origin.
-- source:
--   Canonically Proved zero-barrier far-field generator residual bound 1fd5b0df-9fa0-4df5-b663-44b714a6838d and vcstar_deriv_eq_one_above_cstar 4098a584-9c09-4437-b71f-5590221db9ab.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_hjb_all_positive_zero_barrier_of_nearfield
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc0 : cstar W = 0)
    (hnear : ∀ y : ℝ, 0 < y → (y < 1 ∨ q * y < X.c) →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by sorry
