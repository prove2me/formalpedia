-- Prove2me | Theorems.Thm_FiniteAnchorListPolygonalScreening
-- name    : FiniteAnchorListPolygonalScreening
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:20:30.598537+00:00
-- url     : https://prove2.me/theorems/99ee0640-55f9-4308-9d35-e66b00d40b6f
-- title:
--   Finite anchor-list polygonal screening
-- statement:
--   For a positive radius and a finite anchor list of length at least three, beginning at a and ending at target, one can perturb the list to a same-length vertex list beginning and ending at those points, staying within the prescribed radius at every index and satisfying the point-avoidance, non-overlap, and interior transversality conditions for every consecutive segment relative to a finite polygonal set K.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FiniteAnchorListPolygonalScreening.lean#L1-L195

import Definitions.Def_FinitePolygonalSet
open Classical
noncomputable section

lemma FiniteAnchorListPolygonalScreening
    (K : FinitePolygonalSet) (a target : EuclideanSpace ℝ (Fin 2))
    (anchors : List (EuclideanSpace ℝ (Fin 2))) (ρ : ℝ) :
    0 < ρ →
      a ∉ K.carrier →
        target ∉ K.carrier →
          (∀ _h : 0 < anchors.length, dist a anchors[0] < ρ) →
            anchors.getLast? = some target →
              3 ≤ anchors.length →
                ∃ xs : List (EuclideanSpace ℝ (Fin 2)),
                  xs.length = anchors.length ∧
                    xs.head? = some a ∧
                      xs.getLast? = some target ∧
                        (∀ (i : ℕ) (hxi : i < xs.length) (hai : i < anchors.length),
                          dist xs[i] anchors[i] < ρ) ∧
                          (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ xs → v ∉ K.carrier) ∧
                            (∀ (i : ℕ) (hi : i + 1 < xs.length)
                                (p : EuclideanSpace ℝ (Fin 2)),
                                p ∈ K.points → p ∉ segment ℝ xs[i] xs[i + 1]) ∧
                              (∀ (i : ℕ) (hi : i + 1 < xs.length)
                                  (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
                                  s ∈ K.segments →
                                    ¬ ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
                                      segment ℝ p q ⊆
                                        segment ℝ xs[i] xs[i + 1] ∩ segment ℝ s.1 s.2) ∧
                                (∀ (i : ℕ) (hi : i + 1 < xs.length)
                                    (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
                                    (_hs : s ∈ K.segments)
                                    (p : EuclideanSpace ℝ (Fin 2)),
                                    p ∈ openSegment ℝ xs[i] xs[i + 1] →
                                      p ∈ openSegment ℝ s.1 s.2 →
                                        ¬ ∃ c : ℝ,
                                          s.2 - s.1 = c • (xs[i + 1] - xs[i])) := by sorry
