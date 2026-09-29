-- Prove2me | Theorems.Thm_BookProof_KatoRellich_essentiallySelfAdjointOn_add_relBounded
-- name    : BookProof.KatoRellich.essentiallySelfAdjointOn_add_relBounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:30:18.580255+00:00
-- url     : https://prove2.me/theorems/5596344b-24a3-4c8c-bb8e-bf855876750c
-- title:
--   The Lean 4 theorem `essentiallySelfAdjointOn_add_relBounded` in the `ChapterKatoRellichRelative` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `essentiallySelfAdjointOn_add_relBounded` in the `ChapterKatoRellichRelative` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterKatoRellichRelative.lean

-- Generated from ChapterKatoRellichRelative.lean — theorem BookProof.KatoRellich.essentiallySelfAdjointOn_add_relBounded
import Mathlib
import Definitions.Def_ChapterKatoRellichRelative
import Definitions.Def_ChapterEsaClosureCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.KatoRellich.essentiallySelfAdjointOn_add_relBounded [CompleteSpace F] (H B : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (hesa : EssentiallySelfAdjointOn D H) (hB : SymmetricOn D B)
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hrel : ∀ x : D, ‖B x‖ ≤ a * ‖H x‖ + b * ‖(x : F)‖) :
    EssentiallySelfAdjointOn D (H + B) := by sorry
