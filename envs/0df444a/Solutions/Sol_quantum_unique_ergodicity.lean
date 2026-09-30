-- Prove2me | solution 1 for quantum_unique_ergodicity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:23:55.852791+00:00
-- url     : https://prove2.me/submissions/02eb5b42-fa18-4340-8418-138882d49387

import Mathlib

theorem solution (n : ℕ) (hn : 1 ≤ n)
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.IsSymmetric)
    (psi_n : ℕ → EuclideanSpace ℝ (Fin n))
    (hlambda : ∀ k, T (psi_n k) = (k : ℝ) • psi_n k)
    (hnorm : ∀ k, ‖psi_n k‖ = 1) :
    Filter.Tendsto (fun k =>
      fun A : Set (EuclideanSpace ℝ (Fin n)) =>
        (MeasureTheory.volume A).toReal * ‖psi_n k‖^2)
    Filter.atTop (nhds (fun A => (MeasureTheory.volume A).toReal)) := by
  have hconst : (fun k => fun A : Set (EuclideanSpace ℝ (Fin n)) =>
      (MeasureTheory.volume A).toReal * ‖psi_n k‖^2)
      = fun _ => fun A : Set (EuclideanSpace ℝ (Fin n)) => (MeasureTheory.volume A).toReal := by
    funext k A
    rw [hnorm k]
    ring
  rw [hconst]
  exact tendsto_const_nhds
