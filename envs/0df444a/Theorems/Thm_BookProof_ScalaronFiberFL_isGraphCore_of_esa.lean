-- Prove2me | Theorems.Thm_BookProof_ScalaronFiberFL_isGraphCore_of_esa
-- name    : BookProof.ScalaronFiberFL.isGraphCore_of_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T19:42:58.729554+00:00
-- url     : https://prove2.me/theorems/886d106d-cdee-40cd-9198-ec5090941720
-- title:
--   The Lean 4 theorem `isGraphCore_of_esa` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isGraphCore_of_esa` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronFiberFL.lean

-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.isGraphCore_of_esa
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine
open BookProof.QgOuterFockFL
open BookProof.QgOuterFockCoreFL

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ScalaronFiberFL.isGraphCore_of_esa (C : Comparison F) (C₀ : Submodule ℂ F)
    (hle : C₀ ≤ C.dom) (P : C₀ →ₗ[ℂ] F)
    (hext : ∀ p : C₀, C.op ⟨(p : F), hle p.2⟩ = P p)
    (hesa : EssentiallySelfAdjointOn C₀ P) : IsGraphCore C C₀ := by sorry
