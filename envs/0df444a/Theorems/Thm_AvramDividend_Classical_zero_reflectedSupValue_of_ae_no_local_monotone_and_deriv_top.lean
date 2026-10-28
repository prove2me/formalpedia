-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_ae_no_local_monotone_and_deriv_top
-- name    : AvramDividend.Classical.zero_reflectedSupValue_of_ae_no_local_monotone_and_deriv_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:52:58.534087+00:00
-- url     : https://prove2.me/theorems/4cf38119-3562-44d2-b5fb-9fd60f7d6209
-- title:
--   Zero reflected-supremum value from pathwise non-monotonicity and infinite scale slope
-- statement:
--   If almost every spectrally negative Lévy path is non-monotone on every interval [0,ε], then the first strictly positive drawdown occurs at time zero. The stopped Stieltjes dividend reward is therefore zero. If the scale function right derivative at zero is positive infinity, the corresponding totalised zero-barrier scale candidate is also zero. This proves a reusable conditional branch of the full zero-reflected-supremum identity, including bounded-variation infinite-activity situations once path regularity and scale-slope divergence are established.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, zero barrier case following (3.13), https://arxiv.org/pdf/math/0702893

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_no_local_monotone_path
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_derivZeroPlus_top

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The instant-ruin zero-barrier branch whenever the scale normaliser is infinite. -/
theorem zero_reflectedSupValue_of_ae_no_local_monotone_and_deriv_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hNoMono : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ¬ MonotoneOn (fun t : ℝ≥0 => X.X t ω) (Icc 0 ε))
    (hder : derivZeroPlus W = ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by sorry

end AvramDividend.Classical
