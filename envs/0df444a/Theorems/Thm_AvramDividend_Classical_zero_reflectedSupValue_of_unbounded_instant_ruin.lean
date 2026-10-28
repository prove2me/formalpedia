-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_unbounded_instant_ruin
-- name    : AvramDividend.Classical.zero_reflectedSupValue_of_unbounded_instant_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:40:37.605988+00:00
-- url     : https://prove2.me/theorems/87b35c09-d990-4532-acdc-e600ae006fa8
-- title:
--   Zero reflected value in the unbounded-variation instantaneous-ruin branch
-- statement:
--   For unbounded variation, the q-scale function is zero at the origin by canonical chat04_scale_zero_origin_of_unbounded_variation, hence the zero-barrier analytic candidate vanishes. If the true zero-barrier reflected drawdown ruin time is zero almost surely, the actual stopped Stieltjes reward also vanishes by the separately authored lemma. This is an exact branch of the open zero_reflectedSupValue_eq_barrierValue target. The remaining stochastic task is to prove almost-sure instantaneous downcrossing for unbounded-variation spectrally negative Lévy paths; bounded variation needs independent treatment.
-- source:
--   Combines canonical chat04_scale_zero_origin_of_unbounded_variation with authored barrierValue_zero_of_scale_zero and barrierSupValue_zero_of_ae_instant_ruin. Child of zero_reflectedSupValue_eq_barrierValue.

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_zero
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_reflectedSupValue_of_unbounded_instant_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by sorry
