-- Prove2me | solution 1 for furstenberg_x2_x3_conjecture
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T02:48:30.68739+00:00
-- url     : https://prove2.me/submissions/2c758193-b2d5-45ef-b017-e4aec1b75643

import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory

theorem solution : ¬ (∀ (mu2 : Measure (AddCircle (1 : ℝ))),
    mu2 Set.univ = 1 →
    (∀ S : Set (AddCircle (1 : ℝ)), MeasurableSet S →
      mu2 S = mu2 (Set.preimage (fun x => (2 : ℤ) • x) S)) →
    (∀ S : Set (AddCircle (1 : ℝ)), MeasurableSet S →
      mu2 S = mu2 (Set.preimage (fun x => (3 : ℤ) • x) S)) →
    mu2 = volume) := by
  intro h
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hinv (k : ℤ) (S : Set (AddCircle (1 : ℝ))) (hS : MeasurableSet S) :
      Measure.dirac (0 : AddCircle (1 : ℝ)) S =
        Measure.dirac 0 ((fun x => k • x) ⁻¹' S) := by
    by_cases hzero : (0 : AddCircle (1 : ℝ)) ∈ S
    · simp [Measure.dirac_apply, hzero]
    · simp [Measure.dirac_apply, hzero]
  have heq := h (Measure.dirac 0) (by simp) (hinv 2) (hinv 3)
  have hmass := congrArg (fun mu : Measure (AddCircle (1 : ℝ)) => mu {0}) heq
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) {0} = 0 := by
    rw [← Metric.closedBall_zero (x := (0 : AddCircle (1 : ℝ))),
      AddCircle.volume_closedBall]
    simp
  simpa [hvol] using hmass

#print axioms solution
