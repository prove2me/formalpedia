-- Prove2me | Theorems.Thm_BookProof_KatoRellich_dense_range_add_bounded
-- name    : BookProof.KatoRellich.dense_range_add_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T14:13:15.157843+00:00
-- url     : https://prove2.me/theorems/66b53970-630c-4754-b70c-3cad748419ca
-- title:
--   `BookProof.KatoRellich.dense_range_add_bounded` (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (B : F →L[ℂ] F) (e : ℝ) (he : ‖B‖ < |e|) (hdense : Dense (Set.range fun x : D => H x - ((e :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterKatoRellichDeficiency`.
--
--   `BookProof.KatoRellich.dense_range_add_bounded` (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (B : F →L[ℂ] F) (e : ℝ) (he : ‖B‖ < |e|) (hdense : Dense (Set.range fun x : D => H x - ((e : ℂ) * Complex.I) • (x : F))) : Dense (Set.range fun x : D => (H x + B (x : F)) - ((e : ℂ) * Complex.I) • (x : F))
--
--   Formalization note: Lean 4 identifier `BookProof.KatoRellich.dense_range_add_bounded`.

-- Generated from ChapterKatoRellichDeficiency.lean — theorem BookProof.KatoRellich.dense_range_add_bounded
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterFarisLavineCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.KatoRellich.dense_range_add_bounded (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H)
    (B : F →L[ℂ] F) (e : ℝ) (he : ‖B‖ < |e|)
    (hdense : Dense (Set.range fun x : D => H x - ((e : ℂ) * Complex.I) • (x : F))) :
    Dense (Set.range fun x : D => (H x + B (x : F)) - ((e : ℂ) * Complex.I) • (x : F)) := by sorry
