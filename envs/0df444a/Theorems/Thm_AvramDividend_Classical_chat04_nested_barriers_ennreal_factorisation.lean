-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_nested_barriers_ennreal_factorisation
-- name    : AvramDividend.Classical.chat04_nested_barriers_ennreal_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:35:23.175727+00:00
-- url     : https://prove2.me/theorems/ed426f5d-8465-4b99-a695-9c1775961b29
-- title:
--   Nested two-sided scale factors multiply exactly in ENNReal
-- statement:
--   The scale exit factorisation remains an exact product after converting both factors into the extended nonnegative reals used by Prove2Me's stochastic exit expectations. The q-scale is nonnegative at x and strictly positive at the intermediate barrier a, so ENNReal.ofReal respects multiplication. This is the properly typed factorisation needed to compose nested two-sided discounted exit transforms when the stochastic identity becomes available.
-- source:
--   The newly Proved nested real scale ratio factorisation, with Mathlib's nonnegative-real embedding multiplicativity.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_chat04_nested_barriers_scale_exit_factorisation

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_nested_barriers_ennreal_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x a b : ℝ)
    (hx0 : 0 ≤ x) (hxa : x ≤ a) (ha : 0 < a) (hab : a ≤ b) :
    ENNReal.ofReal (W x / W b) =
      ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a / W b) := by sorry
