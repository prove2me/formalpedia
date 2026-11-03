-- Prove2me | solution 1 for levy_foundations_poissonPieceProductIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:43:07.891515+00:00
-- url     : https://prove2.me/submissions/8c01c806-29da-4923-994a-510db8c5d5d6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Definitions.Def_levy_foundations_isPoissonPointFamily

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k : ℕ) (w : E → ℂ)
    (hw : Measurable w) (hbdd : ∀ x, ‖w x‖ ≤ 1) :
    Integrable (fun ω =>
      ∏ n ∈ Finset.range (K k ω), w (X k n ω)) μ := by
  classical
  have hPmeas : Measurable fun ω =>
      ∏ n ∈ Finset.range (K k ω), w (X k n ω) := by
    have hp : Measurable fun p : Ω × ℕ =>
        ∏ n ∈ Finset.range p.2, w (X k n p.1) :=
      measurable_from_prod_countable_left fun j =>
        Finset.measurable_prod (Finset.range j) fun n _ =>
          hw.comp (hd.measurable_point k n)
    exact hp.comp (measurable_id.prodMk (hd.measurable_count k))
  have hbound : ∀ ω,
      ‖∏ n ∈ Finset.range (K k ω), w (X k n ω)‖ ≤ 1 := by
    intro ω
    calc ‖∏ n ∈ Finset.range (K k ω), w (X k n ω)‖
        = ∏ n ∈ Finset.range (K k ω), ‖w (X k n ω)‖ := norm_prod _ _
      _ ≤ 1 := Finset.prod_le_one
        (fun _ _ => norm_nonneg _) (fun _ _ => hbdd _)
  exact (integrable_const (1 : ℝ)).mono'
    hPmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
