-- Prove2me | Theorems.Thm_AvramDividend_Classical_restrictedMapLaw_event_marginal_factor
-- name    : AvramDividend.Classical.restrictedMapLaw_event_marginal_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:00:40.472637+00:00
-- url     : https://prove2.me/theorems/f2cff3c4-e6ba-4ab0-92c3-ede656bfd82d
-- title:
--   Restricted path laws imply event-marginal independence equations
-- statement:
--   If the pushforward law of a measurable random element Y under restriction to event A equals the event probability times the original pushforward law, then every measurable marginal set B satisfies P(A∩{Y∈B})=P(A)P(Y∈B).
-- source:
--   Measure-algebra bridge from finite-stopping restricted future-path strong Markov laws (3075481a-89a4-4c24-b131-2afd90b66eea) to the event-independence criterion required by canonical joint law 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and dividend split 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Set

theorem AvramDividend.Classical.restrictedMapLaw_event_marginal_factor
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) (Y : Ω → β) (hY : Measurable Y)
    (A : Set Ω)
    (hLaw : Measure.map Y (P.restrict A) =
      (P A) • Measure.map Y P)
    (B : Set β) (hB : MeasurableSet B) :
    P (A ∩ Y ⁻¹' B) = P A * P (Y ⁻¹' B) := by
  sorry
