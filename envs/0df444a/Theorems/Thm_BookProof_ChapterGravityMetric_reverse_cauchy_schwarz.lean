-- Prove2me | Theorems.Thm_BookProof_ChapterGravityMetric_reverse_cauchy_schwarz
-- name    : BookProof.ChapterGravityMetric.reverse_cauchy_schwarz
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:59:58.352854+00:00
-- url     : https://prove2.me/theorems/c621e199-a15f-48b4-b8d7-f472a0142ec2
-- title:
--   `BookProof.ChapterGravityMetric.reverse_cauchy_schwarz` (v x : Fin 4 → ℝ) (hv : minkSq v = -1) : 0 ≤ (∑ a, x a * lower v a) ^ 2 + minkSq x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityMetric`.
--
--   `BookProof.ChapterGravityMetric.reverse_cauchy_schwarz` (v x : Fin 4 → ℝ) (hv : minkSq v = -1) : 0 ≤ (∑ a, x a * lower v a) ^ 2 + minkSq x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityMetric.reverse_cauchy_schwarz`.

-- Generated from ChapterGravityMetric.lean — theorem BookProof.ChapterGravityMetric.reverse_cauchy_schwarz
import Mathlib
import Definitions.Def_ChapterGravityMetric
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityMetric.reverse_cauchy_schwarz (v x : Fin 4 → ℝ) (hv : minkSq v = -1) :
    0 ≤ (∑ a, x a * lower v a) ^ 2 + minkSq x := by sorry
