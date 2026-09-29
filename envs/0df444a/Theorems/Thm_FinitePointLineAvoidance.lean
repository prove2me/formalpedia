-- Prove2me | Theorems.Thm_FinitePointLineAvoidance
-- name    : FinitePointLineAvoidance
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T19:19:04.363986+00:00
-- url     : https://prove2.me/theorems/f95f6171-f042-46c7-964c-de0959520aef
-- title:
--   Avoiding finitely many points and affine lines in an open planar set
-- statement:
--   Let $W$ be a nonempty open subset of the Euclidean plane. Given a finite set of forbidden points and a finite family of affine lines, each of genuine one-dimensional direction, there exists a point of $W$ that avoids every forbidden point and every listed line. This is the finite-avoidance principle used to choose a generic bend point for polygonal paths.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FinitePointLineAvoidance.lean#L1-L74

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Baire.Lemmas

open Classical
noncomputable section

lemma FinitePointLineAvoidance
    (W : Set (EuclideanSpace ℝ (Fin 2)))
    (points : Finset (EuclideanSpace ℝ (Fin 2)))
    (lines : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hWopen : IsOpen W) (hWnonempty : W.Nonempty)
    (hline : ∀ ℓ ∈ lines,
      (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty ∧
        Module.finrank ℝ ℓ.direction = 1) :
    ∃ x ∈ W, x ∉ (points : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ∀ ℓ ∈ lines, x ∉ (ℓ : Set (EuclideanSpace ℝ (Fin 2))) := by sorry
