-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_positive_poisson_mass_ae_cylinder
-- name    : AvramDividend.Classical.chat06_positive_poisson_mass_ae_cylinder
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:57:27.437802+00:00
-- url     : https://prove2.me/theorems/235a74aa-2c8d-400a-9abc-a9c6721c9880
-- title:
--   Poisson singleton mass from almost-sure Erlang arrival cylinders
-- statement:
--   Under the exact successive Erlang survival laws and almost-sure inclusion of arrival events, the real probability of a given positive Poisson count has the expected exponential-factorial mass.
-- source:
--   Chat 06 standalone Lean source with verified private remote pinned compiler elaboration; exact SHA and job in SUBMISSIONS.json, no official proof yet.

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_positive_poisson_mass_ae_cylinder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (E A B : Set Ω) (n : ℕ) (t : ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hSub : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ B)
    (hEvent : (fun ω : Ω => ω ∈ E) =ᵐ[P]
      (fun ω : Ω => ω ∈ B \ A))
    (hTailA : P.real A = Real.exp (-t) *
      ∑ j ∈ Finset.range (n + 1), t ^ j / (j.factorial : ℝ))
    (hTailB : P.real B = Real.exp (-t) *
      ∑ j ∈ Finset.range (n + 2), t ^ j / (j.factorial : ℝ)) :
    P.real E = Real.exp (-t) * t ^ (n + 1) /
      ((n + 1).factorial : ℝ) := by sorry
