-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlap_coherentOverlap_eq
-- name    : BookProof.ChapterCoherentOverlap.coherentOverlap_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:59:12.357253+00:00
-- url     : https://prove2.me/theorems/8df0b7ec-a86c-4cea-92a0-16292cae43cc
-- title:
--   `BookProof.ChapterCoherentOverlap.coherentOverlap_eq` (q k : EuclideanSpace ℝ (Fin n)) : coherentOverlap q k = Real.exp (-(∑ i, q i * q i) / 2 - (∑ i, k i * k i) / 2 + ∑ i, q i * k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlap`.
--
--   `BookProof.ChapterCoherentOverlap.coherentOverlap_eq` (q k : EuclideanSpace ℝ (Fin n)) : coherentOverlap q k = Real.exp (-(∑ i, q i * q i) / 2 - (∑ i, k i * k i) / 2 + ∑ i, q i * k i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlap.coherentOverlap_eq`.

-- Generated from ChapterCoherentOverlap.lean — theorem BookProof.ChapterCoherentOverlap.coherentOverlap_eq
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.ChapterCoherentOverlap


open scoped BigOperators

noncomputable section


variable {n : ℕ}

theorem BookProof.ChapterCoherentOverlap.coherentOverlap_eq (q k : EuclideanSpace ℝ (Fin n)) :
    coherentOverlap q k =
      Real.exp (-(∑ i, q i * q i) / 2 - (∑ i, k i * k i) / 2 + ∑ i, q i * k i) := by sorry
