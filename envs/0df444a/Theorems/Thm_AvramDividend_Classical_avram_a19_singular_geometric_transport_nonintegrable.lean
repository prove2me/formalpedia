-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_transport_nonintegrable
-- name    : AvramDividend.Classical.avram_a19_singular_geometric_transport_nonintegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:54:59.850928+00:00
-- url     : https://prove2.me/theorems/926832da-6ae7-4364-bf3a-de4c8e2f94ae
-- title:
--   Geometric singular generator loss remains nonintegrable after measure-preserving sampling
-- statement:
--   If the natural-valued random variable K on an arbitrary measure space has the half-geometric distribution, and the postpayment surplus at index k obeys the dyadic square bound, the transported singular generator loss remains nonintegrable. This reduces the full stochastic countermodel to a source-exact pushforward law and surplus identification.
-- source:
--   A19 source-exact countermodel transport, 7 November 2026; uses Proved public geometric singular nonintegrability lemma 3adb6269.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_not_integrable
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_a19_singular_geometric_transport_nonintegrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : unitInterval) (hp : p != 0) (hhalf : (p : Real) = 1 / 2)
    (K : Ω → Nat)
    (hK : MeasurePreserving K P (geometricMeasure p))
    (y : Nat → Real)
    (hy : forall k, 0 < y k)
    (hsmall : forall k, y k <= 1 / 16)
    (hpower : forall k, y k <= 1 / ((2 : Real) ^ k) ^ 2) :
    Not (Integrable (fun ω =>
      -(3 + y (K ω) - 4 * Real.sqrt (y (K ω)) -
        2 / Real.sqrt (y (K ω)))) P) := by sorry
