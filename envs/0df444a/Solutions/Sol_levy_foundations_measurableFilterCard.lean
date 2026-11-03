-- Prove2me | solution 1 for levy_foundations_measurableFilterCard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:21:09.272801+00:00
-- url     : https://prove2.me/submissions/7d8da05a-346c-4d8b-b7d9-1d90a8231d9d

import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open Classical in

theorem solution
    {D E : Type*} [MeasurableSpace D] [MeasurableSpace E]
    (A : Set E) (hA : MeasurableSet A)
    (cnt : D → ℕ) (pt : ℕ → D → E)
    (hcnt : Measurable cnt) (hpt : ∀ n, Measurable (pt n)) :
    Measurable (fun g => ((Finset.range (cnt g)).filter
      (fun n => pt n g ∈ A)).card) := by
  classical
  have hcard :
      (fun g => ((Finset.range (cnt g)).filter
        (fun n => pt n g ∈ A)).card) =
      fun g => ∑ n ∈ Finset.range (cnt g),
        (if pt n g ∈ A then (1 : ℕ) else 0) := by
    funext g
    rw [Finset.card_filter]
  rw [hcard]
  have hP : Measurable (fun p : D × ℕ =>
      ∑ n ∈ Finset.range p.2,
        (if pt n p.1 ∈ A then (1 : ℕ) else 0)) :=
    measurable_from_prod_countable_left fun j =>
      Finset.measurable_sum (Finset.range j) fun n _ =>
        Measurable.ite (hpt n hA) measurable_const measurable_const
  exact hP.comp (measurable_id.prodMk hcnt)
