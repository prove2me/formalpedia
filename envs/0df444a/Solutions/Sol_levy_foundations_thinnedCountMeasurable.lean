-- Prove2me | solution 1 for levy_foundations_thinnedCountMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:13:09.883991+00:00
-- url     : https://prove2.me/submissions/7329a499-e528-413b-bb8d-761550a2f026

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_levy_foundations_thinnedCount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (A : Set E) (k : ℕ) (hK : Measurable (K k))
    (hX : ∀ n, Measurable (X k n)) (hA : MeasurableSet A) :
    Measurable (LevyFoundations.thinnedCount K X A k) := by
  classical
  have hcard : LevyFoundations.thinnedCount K X A k =
      fun ω => ∑ n ∈ Finset.range (K k ω),
        (if X k n ω ∈ A then (1 : ℕ) else 0) := by
    funext ω
    rw [LevyFoundations.thinnedCount, Finset.card_filter]
  rw [hcard]
  have hsum : Measurable fun p : Ω × ℕ =>
      ∑ n ∈ Finset.range p.2,
        (if X k n p.1 ∈ A then (1 : ℕ) else 0) :=
    measurable_from_prod_countable_left fun j =>
      Finset.measurable_sum (Finset.range j) fun n _ =>
        Measurable.ite (hX n hA) measurable_const measurable_const
  exact hsum.comp (measurable_id.prodMk hK)
