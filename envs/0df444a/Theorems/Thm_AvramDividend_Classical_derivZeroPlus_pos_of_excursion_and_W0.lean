-- Prove2me | Theorems.Thm_AvramDividend_Classical_derivZeroPlus_pos_of_excursion_and_W0
-- name    : AvramDividend.Classical.derivZeroPlus_pos_of_excursion_and_W0
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T18:07:06.910409+00:00
-- url     : https://prove2.me/theorems/cddbc1c6-108a-4f3f-9d1c-c4e0295ce17d
-- title:
--   Positive boundary value plus the excursion derivative identity forces a positive right derivative liminf
-- statement:
--   If W(0)>0, W is nondecreasing on [0,∞), and for x>0 its derivative has the excursion form W'(x)=W(x)(φ+μ([x,∞))) with φ>0, then W'(x) is uniformly bounded below by φW(0)>0 on the positive half-line. Hence the extended-real right liminf of W' at zero is strictly positive.
-- source:
--   Elementary order argument plus Proved deriv_global_lower_le_right_liminf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_deriv_global_lower_le_right_liminf
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.derivZeroPlus_pos_of_excursion_and_W0
    (W : ℝ → ℝ) (φ : ℝ) (μ : Measure ℝ)
    (hφ : 0 < φ) (hW0 : 0 < W 0)
    (hmono : MonotoneOn W (Ici 0))
    (hrepr : ∀ x : ℝ, 0 < x →
      deriv W x = W x * (φ + μ.real (Ici x))) :
    (0 : EReal) < derivZeroPlus W := by sorry
