-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_independent_stream_integral_disintegration_20261111
-- name    : AvramDividend.Classical.avram_a06_independent_stream_integral_disintegration_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:03:28.656687+00:00
-- url     : https://prove2.me/theorems/d5f66225-15d3-4090-a646-49c0323f44b6
-- title:
--   Integrate an independent count and mark stream by iterated pushforward integrals
-- statement:
--   If a count vector and entire mark stream are independent measurable random elements, any integrable complex observable of both admits iterated integration against the product of their marginal laws. This is the reusable measure-theoretic disintegration step for conditional Fourier representation 5d7ad8be. Proof from Mathlib IndepFun.map_prod_eq_prod_map_map, integral_map and Fubini integral_prod.

import Mathlib
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_a06_independent_stream_integral_disintegration_20261111
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y) (hIndep : IndepFun X Y P)
    (F : A × B → ℂ)
    (hF : Integrable F ((Measure.map X P).prod (Measure.map Y P))) :
    (∫ ω, F (X ω, Y ω) ∂P) =
      ∫ a, ∫ b, F (a, b) ∂(Measure.map Y P) ∂(Measure.map X P) := by sorry
