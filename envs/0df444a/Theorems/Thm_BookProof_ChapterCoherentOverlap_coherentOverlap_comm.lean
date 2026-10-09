-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlap_coherentOverlap_comm
-- name    : BookProof.ChapterCoherentOverlap.coherentOverlap_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:59:46.003617+00:00
-- url     : https://prove2.me/theorems/d471faf6-a4a9-463c-b950-0d7b74eb729c
-- title:
--   `BookProof.ChapterCoherentOverlap.coherentOverlap_comm` (q k : EuclideanSpace ℝ (Fin n)) : coherentOverlap q k = coherentOverlap k q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlap`.
--
--   `BookProof.ChapterCoherentOverlap.coherentOverlap_comm` (q k : EuclideanSpace ℝ (Fin n)) : coherentOverlap q k = coherentOverlap k q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlap.coherentOverlap_comm`.

-- Generated from ChapterCoherentOverlap.lean — theorem BookProof.ChapterCoherentOverlap.coherentOverlap_comm
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlap


open scoped BigOperators

noncomputable section


variable {n : ℕ}

theorem BookProof.ChapterCoherentOverlap.coherentOverlap_comm (q k : EuclideanSpace ℝ (Fin n)) :
    coherentOverlap q k = coherentOverlap k q := by sorry
