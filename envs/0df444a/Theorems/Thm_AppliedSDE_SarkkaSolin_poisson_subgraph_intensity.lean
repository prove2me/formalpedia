-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_poisson_subgraph_intensity
-- name    : AppliedSDE.SarkkaSolin.poisson_subgraph_intensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:42:05.902083+00:00
-- url     : https://prove2.me/theorems/b0ea49c6-02d8-4c2d-9330-9885092176c4
-- title:
--   Marked-Poisson subgraph intensity is integral of its threshold
-- statement:
--   For a continuous threshold between 0 and M on [0,T], its closed subgraph has two-dimensional Lebesgue area equal to the integral of the threshold, expressed as a finite Poisson intensity. Necessary for parent Poisson void theorem eb448c4a-408f-4275-8349-455b4869786e in SDE Chapter 8.
-- source:
--   Sarkka and Solin (2019), Chapter 8. Parent eb448c4a-408f-4275-8349-455b4869786e.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem AppliedSDE.SarkkaSolin.poisson_subgraph_intensity
    (T M : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (φ : ℝ -> ℝ) (hφ : Continuous φ)
    (hφ0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ φ t)
    (hφM : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ M) :
    let A : Set (ℝ × ℝ) :=
      {z | z.1 ∈ Set.Icc (0 : ℝ) T ∧ z.2 ∈ Set.Icc 0 (φ z.1)}
    ((volume : Measure (ℝ × ℝ)).restrict
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) M)) A =
      ENNReal.ofReal (∫ t in (0 : ℝ)..T, φ t) := by
  sorry
