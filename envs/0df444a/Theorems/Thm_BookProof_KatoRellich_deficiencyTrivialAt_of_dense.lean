-- Prove2me | Theorems.Thm_BookProof_KatoRellich_deficiencyTrivialAt_of_dense
-- name    : BookProof.KatoRellich.deficiencyTrivialAt_of_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T14:12:52.740083+00:00
-- url     : https://prove2.me/theorems/b8b68b38-2b57-452a-9ce6-6789482f0e7c
-- title:
--   `BookProof.KatoRellich.deficiencyTrivialAt_of_dense` (T : D →ₗ[ℂ] F) (z : ℂ) (hd : Dense (Set.range fun x : D => T x - ((starRingEnd ℂ) z) • (x : F))) : DeficiencyTrivialAt D T z
-- statement:
--   Prove the following Lean 4 theorem from `ChapterKatoRellichDeficiency`.
--
--   `BookProof.KatoRellich.deficiencyTrivialAt_of_dense` (T : D →ₗ[ℂ] F) (z : ℂ) (hd : Dense (Set.range fun x : D => T x - ((starRingEnd ℂ) z) • (x : F))) : DeficiencyTrivialAt D T z
--
--   Formalization note: Lean 4 identifier `BookProof.KatoRellich.deficiencyTrivialAt_of_dense`.

-- Generated from ChapterKatoRellichDeficiency.lean — theorem BookProof.KatoRellich.deficiencyTrivialAt_of_dense
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterFarisLavineCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.KatoRellich.deficiencyTrivialAt_of_dense (T : D →ₗ[ℂ] F) (z : ℂ)
    (hd : Dense (Set.range fun x : D => T x - ((starRingEnd ℂ) z) • (x : F))) :
    DeficiencyTrivialAt D T z := by sorry
