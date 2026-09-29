-- Prove2me | Theorems.Thm_BookProof_KatoRellich_dense_range_add_relBounded
-- name    : BookProof.KatoRellich.dense_range_add_relBounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:28:10.597025+00:00
-- url     : https://prove2.me/theorems/c3edba73-6185-435a-aece-79fc947d9a13
-- title:
--   The Lean 4 theorem `dense_range_add_relBounded` in the `ChapterKatoRellichRelative` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `dense_range_add_relBounded` in the `ChapterKatoRellichRelative` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterKatoRellichRelative.lean

-- Generated from ChapterKatoRellichRelative.lean — theorem BookProof.KatoRellich.dense_range_add_relBounded
import Mathlib
import Definitions.Def_ChapterKatoRellichRelative
import Definitions.Def_ChapterEsaClosureCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.KatoRellich.dense_range_add_relBounded (H B : D →ₗ[ℂ] F) (hH : SymmetricOn D H) {a b e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : e ≠ 0)
    (hrel : ∀ x : D, ‖B x‖ ≤ a * ‖H x‖ + b * ‖(x : F)‖) (hq1 : a + b / |e| < 1)
    (hdense : Dense (Set.range fun x : D => H x - ((e : ℂ) * Complex.I) • (x : F))) :
    Dense (Set.range fun x : D => (H x + B x) - ((e : ℂ) * Complex.I) • (x : F)) := by sorry
