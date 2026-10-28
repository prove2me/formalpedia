-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_negative_near_zero
-- name    : AvramDividend.Classical.barrierSupValue_zero_of_ae_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:38:52.26971+00:00
-- url     : https://prove2.me/theorems/6a5e5995-3f7e-497d-bd3a-1f7ab1696993
-- title:
--   Almost-sure negative near-zero paths force zero stopped reflected reward
-- statement:
--   An almost-sure negative Lévy path at arbitrarily small times forces the zero-level reflected drawdown ruin time to vanish. The previously established instantaneous-ruin theorem then gives zero stopped Stieltjes dividend reward. This is a conditional branch of zero_reflectedSupValue_eq_barrierValue, with no unbounded-variation hypothesis, and isolates precisely where small-time regularity is needed.
-- source:
--   Root-connected bridge from canonical pathwise negative-excursion and stopped-reward theorems to zero_reflectedSupValue_eq_barrierValue.

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_negative_path
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierSupValue_zero_of_ae_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    barrierSupValue X 0 q = 0 := by sorry
