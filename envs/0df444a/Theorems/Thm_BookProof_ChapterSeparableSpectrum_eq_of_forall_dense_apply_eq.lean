-- Prove2me | Theorems.Thm_BookProof_ChapterSeparableSpectrum_eq_of_forall_dense_apply_eq
-- name    : BookProof.ChapterSeparableSpectrum.eq_of_forall_dense_apply_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:40:55.873073+00:00
-- url     : https://prove2.me/theorems/86f2b6ca-a2e5-4339-9505-97f674147300
-- title:
--   `BookProof.ChapterSeparableSpectrum.eq_of_forall_dense_apply_eq` {D : Set C(Y, ℂ)} (hD : Dense D) {y₁ y₂ : Y} (h : ∀ d ∈ D, (d : C(Y, ℂ)) y₁ = d y₂) : y₁ = y₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSeparableSpectrum`.
--
--   `BookProof.ChapterSeparableSpectrum.eq_of_forall_dense_apply_eq` {D : Set C(Y, ℂ)} (hD : Dense D) {y₁ y₂ : Y} (h : ∀ d ∈ D, (d : C(Y, ℂ)) y₁ = d y₂) : y₁ = y₂
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSeparableSpectrum.eq_of_forall_dense_apply_eq`.

-- Generated from ChapterSeparableSpectrum.lean — theorem BookProof.ChapterSeparableSpectrum.eq_of_forall_dense_apply_eq
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterStandardBorelClassification
import Mathlib
import Definitions.Def_ChapterSeparableSpectrum
open BookProof.ChapterSeparableSpectrum


noncomputable section

open MeasureTheory TopologicalSpace WeakDual


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianDirectSum
open BookProof.ChapterStandardBorelClassification

variable (Y : Type*) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]

theorem BookProof.ChapterSeparableSpectrum.eq_of_forall_dense_apply_eq {D : Set C(Y, ℂ)} (hD : Dense D) {y₁ y₂ : Y}
    (h : ∀ d ∈ D, (d : C(Y, ℂ)) y₁ = d y₂) : y₁ = y₂ := by sorry
