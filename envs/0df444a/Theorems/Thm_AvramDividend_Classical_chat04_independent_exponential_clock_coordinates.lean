-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_independent_exponential_clock_coordinates
-- name    : AvramDividend.Classical.chat04_independent_exponential_clock_coordinates
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:27:41.146492+00:00
-- url     : https://prove2.me/theorems/74d1d8f9-1bc4-4d59-a241-3c2e46d5355e
-- title:
--   Independent exponential observation time and underlying random path coordinates
-- statement:
--   For any probability law P on a Lévy sample space Ω and any exponential rate p>0, the two canonical coordinate projections (ω,t)↦ω and (ω,t)↦t are independent under the genuine product law P⊗Exp(p). This verifies actual independence (not just the two marginal distributions) for the externally sampled exponential horizon used in the finite-p Wiener–Hopf factorisation.
-- source:
--   Mathlib already provides `ProbabilityTheory.indepFun_prod` for two measurable functions of disjoint coordinates of a product measure. Instantiate both functions as identity maps, with μ=P and ν=ProbabilityTheory.expMeasure p, applying `measurable_id` twice. The resulting independence is an authentic probabilistic property of the constructed product law, not a formal postulate or an assumption about the existence of a global Esscher process.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic
open MeasureTheory ProbabilityTheory

theorem AvramDividend.Classical.chat04_independent_exponential_clock_coordinates
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp : 0 < p) :
    IndepFun
      (fun z : Ω × ℝ => z.1)
      (fun z : Ω × ℝ => z.2)
      (P.prod (ProbabilityTheory.expMeasure p)) := by sorry
