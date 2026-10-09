-- Prove2me | Theorems.Thm_BookProof_ChapterGravityProjDirectSum_isCompl_range_of_add_eq_id
-- name    : BookProof.ChapterGravityProjDirectSum.isCompl_range_of_add_eq_id
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:48:49.785128+00:00
-- url     : https://prove2.me/theorems/314e2c40-8a38-4fda-bad9-54a4f3fb8937
-- title:
--   `BookProof.ChapterGravityProjDirectSum.isCompl_range_of_add_eq_id` {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (P Q : V →ₗ[R] V) (hsum : P + Q = LinearMap.id) (hPQ : P
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityProjDirectSum`.
--
--   `BookProof.ChapterGravityProjDirectSum.isCompl_range_of_add_eq_id` {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (P Q : V →ₗ[R] V) (hsum : P + Q = LinearMap.id) (hPQ : P.comp Q = 0) (hQP : Q.comp P = 0) : IsCompl (LinearMap.range P) (LinearMap.range Q)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityProjDirectSum.isCompl_range_of_add_eq_id`.

-- Generated from ChapterGravityProjDirectSum.lean — theorem BookProof.ChapterGravityProjDirectSum.isCompl_range_of_add_eq_id
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterGravityTimeProj
import Mathlib
import Definitions.Def_ChapterGravityProjDirectSum
open BookProof.ChapterGravityProjDirectSum


open Matrix


open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

theorem BookProof.ChapterGravityProjDirectSum.isCompl_range_of_add_eq_id {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (P Q : V →ₗ[R] V) (hsum : P + Q = LinearMap.id)
    (hPQ : P.comp Q = 0) (hQP : Q.comp P = 0) :
    IsCompl (LinearMap.range P) (LinearMap.range Q) := by sorry
