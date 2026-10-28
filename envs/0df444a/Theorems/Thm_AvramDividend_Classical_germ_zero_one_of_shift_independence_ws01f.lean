-- Prove2me | Theorems.Thm_AvramDividend_Classical_germ_zero_one_of_shift_independence_ws01f
-- name    : AvramDividend.Classical.germ_zero_one_of_shift_independence_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:38:46.279287+00:00
-- url     : https://prove2.me/theorems/05828212-3e5d-4193-94c9-6bad44cd3628
-- title:
--   Lévy germ zero-one law from full shifted-path independence and origin continuity
-- statement:
--   A general real-valued process with measurable coordinates and almost-sure right continuity at the origin has a trivial time-zero germ sigma-algebra when its full future shifted-increment process is independent of the entire observable past at every positive time. This is the Blumenthal zero-one theorem in precisely the form needed for a Lévy process. The independent-increment-to-whole-future independence premise remains explicit and must be supplied from accepted Lévy Markov machinery.
-- source:
--   Durrett, Probability: Theory and Examples, Theorem 7.2.3 and accepted Prove2Me Brownian germ zero-one proof eed4be13; the same measure-theoretic argument with the full shifted Lévy independence premise supplied explicitly. Parent Rogozin branch 0b94b9ab and b12c5430.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

open Filter MeasureTheory ProbabilityTheory DurrettProbability
open scoped NNReal Topology

theorem AvramDividend.Classical.germ_zero_one_of_shift_independence_ws01f
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t))
    (hC : ∀ᵐ ω ∂P, Tendsto (fun t => B t ω) (𝓝 0) (𝓝 0))
    (hShift : ∀ s : ℝ≥0, 0 < s →
      Indep
        (MeasurableSpace.comap
          (fun ω (u : ℝ≥0) => B (s + u) ω - B s ω)
          MeasurableSpace.pi)
        (pastSigma B s) P)
    {A : Set Ω} (hA : MeasurableSet[germSigma B] A) :
    P A = 0 ∨ P A = 1 := by sorry
