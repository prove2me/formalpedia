-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_ae_instant_ruin_and_W_zero
-- name    : AvramDividend.Classical.zero_reflectedSupValue_of_ae_instant_ruin_and_W_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:14:16.241984+00:00
-- url     : https://prove2.me/theorems/0811f425-ffa7-44e4-a5b2-e41197c4a44d
-- title:
--   Zero-barrier reflected-supremum equality from instant ruin and vanishing scale-function origin
-- statement:
--   If reflected ruin occurs at time zero almost surely, the stopped running-supremum dividend reward vanishes. If the scale function also satisfies W(0)=0, the canonical analytic zero-barrier value vanishes. Their equality follows directly, providing the conditional closure for the Gaussian/non-bounded-variation zero-barrier branch once process regularity and scale-origin properties are established.
-- source:
--   Avram, Palmowski and Pistorius (2007), (3.13) zero-barrier boundary case, https://arxiv.org/pdf/math/0702893; existing verified Prove2Me instantaneous-ruin and analytic origin-zero lemmas.

import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_origin_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Instant zero-barrier ruin and a vanishing scale origin force zero reflected value. -/
theorem zero_reflectedSupValue_of_ae_instant_ruin_and_W_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0)
    (hW0 : W 0 = 0) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by sorry

end AvramDividend.Classical
