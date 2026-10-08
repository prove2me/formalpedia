-- Prove2me | Theorems.Thm_BookProof_Bosonic_field_comp_selfAdjoint
-- name    : BookProof.Bosonic.field_comp_selfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:08:46.555+00:00
-- url     : https://prove2.me/theorems/23573532-0c85-44d6-bbcc-9e8b08453f2b
-- title:
--   `BookProof.Bosonic.field_comp_selfAdjoint` (h : BosonicCCR J a) (T : V →ₗ[ℝ] V) (v : V) : star (a (T v)) = a (T v)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBosonicCCR`.
--
--   `BookProof.Bosonic.field_comp_selfAdjoint` (h : BosonicCCR J a) (T : V →ₗ[ℝ] V) (v : V) : star (a (T v)) = a (T v)
--
--   Formalization note: Lean 4 identifier `BookProof.Bosonic.field_comp_selfAdjoint`.

-- Generated from ChapterBosonicCCR.lean — theorem BookProof.Bosonic.field_comp_selfAdjoint
import Mathlib
import Definitions.Def_ChapterBosonicCCR
import Definitions.Def_ChapterStoneConverse
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.Bosonic


open RealInnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [Algebra ℝ R]
  [IsScalarTower ℝ ℂ R] [StarModule ℂ R]

variable {J : V →ₗ[ℝ] V} {a : V →ₗ[ℝ] R}

theorem BookProof.Bosonic.field_comp_selfAdjoint (h : BosonicCCR J a) (T : V →ₗ[ℝ] V) (v : V) :
    star (a (T v)) = a (T v) := by sorry
