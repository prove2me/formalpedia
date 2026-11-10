-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gtop21_nnreal_min_max_stopping
-- name    : AvramDividend.Classical.avram_gtop21_nnreal_min_max_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T02:09:02.15761+00:00
-- url     : https://prove2.me/theorems/9f8a7295-aba9-45e1-9fbc-d3e26d6b61bc
-- title:
--   Finite min and max of genuine NNReal stopping clocks retain the original filtration instance
-- statement:
--   Exact local stopping-clock bridge for root-connected Open ed15a6de and its parent 22bf1d41. The original canonical right-continuous filtration on NNReal and its typeclass order instance must be retained. Prove the min and max stopping conditions directly by measurable union and intersection of the two clock threshold events; preserve the actual clocks and avoid a mismatched LinearOrder-derived filtration instance.
-- source:
--   Exposes source-exact repair for remote CE candidate 32560: MeasureTheory.IsStoppingTime.min/max synthesis chooses NNReal LinearOrder-derived Preorder incompatible with the canonical NNReal.instPartialOrder in 𝓕.rightCont. Reuse the same filtration and eventwise stopping-time characterisation.

import Mathlib
import Mathlib.Probability.Process.Stopping
open MeasureTheory
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gtop21_nnreal_min_max_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (a b : Ω → ℝ≥0)
    (ha : IsStoppingTime 𝓕.rightCont (fun ω => (a ω : WithTop ℝ≥0)))
    (hb : IsStoppingTime 𝓕.rightCont (fun ω => (b ω : WithTop ℝ≥0))) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => (min (a ω) (b ω) : WithTop ℝ≥0)) ∧
    IsStoppingTime 𝓕.rightCont
      (fun ω => (max (a ω) (b ω) : WithTop ℝ≥0)) := by sorry
