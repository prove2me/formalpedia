-- Prove2me | solution 1 for thm_8_2
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:48.930425+00:00
-- url     : https://prove2.me/submissions/5efe6ea3-221e-429f-96be-140572cc6bb1

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Tactic

open MeasureTheory


/-- Exported statement for Theorem 8.2: on sigma-finite spaces, the product measure is the
unique measure on the product measurable space agreeing with rectangle masses. -/
theorem solution
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q] :
    ∃! R : Measure (α × β),
      ∀ s : Set α, ∀ t : Set β,
        MeasurableSet s → MeasurableSet t → R (s ×ˢ t) = P s * Q t := by
  refine ⟨P.prod Q, fun s t _ _ => Measure.prod_prod s t, ?_⟩
  intro R hR
  exact (Measure.prod_eq hR).symm

