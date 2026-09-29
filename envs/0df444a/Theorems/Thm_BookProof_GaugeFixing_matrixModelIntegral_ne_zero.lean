-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_matrixModelIntegral_ne_zero
-- name    : BookProof.GaugeFixing.matrixModelIntegral_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:26:43.019502+00:00
-- url     : https://prove2.me/theorems/38976a1e-d9b4-40cf-8933-79513af8c9e9
-- title:
--   The model's evaluation functional is not identically zero
-- statement:
--   The model's evaluation functional is not identically zero.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.matrixModelIntegral_ne_zero` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 383–387.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L383-L387

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.matrixModelIntegral_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.matrixModelIntegral_ne_zero :
    ∃ X : Mat2, matrixModelIntegral.int X ≠ 0 := by sorry
