-- Prove2me | Theorems.Thm_BookProof_ChapterG_gaugeInvariant_iff_factors
-- name    : BookProof.ChapterG.gaugeInvariant_iff_factors
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:45:21.899249+00:00
-- url     : https://prove2.me/theorems/01e1676e-30e2-445b-b2f4-438a3f73814f
-- title:
--   `BookProof.ChapterG.gaugeInvariant_iff_factors` {X Y Z : Type*} {π : X → Y} (hπ : Function.Surjective π) (f : X → Z) : (∀ g ∈ gaugeGroup π, ∀ x, f (g x) = f x) ↔ ∃ h : Y → Z, f = h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG`.
--
--   `BookProof.ChapterG.gaugeInvariant_iff_factors` {X Y Z : Type*} {π : X → Y} (hπ : Function.Surjective π) (f : X → Z) : (∀ g ∈ gaugeGroup π, ∀ x, f (g x) = f x) ↔ ∃ h : Y → Z, f = h ∘ π
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG.gaugeInvariant_iff_factors`.

-- Generated from ChapterG.lean — theorem BookProof.ChapterG.gaugeInvariant_iff_factors
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG


open scoped ComplexConjugate InnerProductSpace Matrix

theorem BookProof.ChapterG.gaugeInvariant_iff_factors {X Y Z : Type*} {π : X → Y}
    (hπ : Function.Surjective π) (f : X → Z) :
    (∀ g ∈ gaugeGroup π, ∀ x, f (g x) = f x) ↔ ∃ h : Y → Z, f = h ∘ π := by sorry
