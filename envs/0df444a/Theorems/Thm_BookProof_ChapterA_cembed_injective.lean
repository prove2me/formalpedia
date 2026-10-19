-- Prove2me | Theorems.Thm_BookProof_ChapterA_cembed_injective
-- name    : BookProof.ChapterA.cembed_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:16:17.519161+00:00
-- url     : https://prove2.me/theorems/97f413e0-07be-4129-8e91-6fd153db02be
-- title:
--   `BookProof.ChapterA.cembed_injective` [Nontrivial V] : Function.Injective (cembed : ℂ → (V →L[ℝ] V))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2c`.
--
--   `BookProof.ChapterA.cembed_injective` [Nontrivial V] : Function.Injective (cembed : ℂ → (V →L[ℝ] V))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.cembed_injective`.

-- Generated from ChapterA2c.lean — theorem BookProof.ChapterA.cembed_injective
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.cembed_injective [Nontrivial V] :
    Function.Injective (cembed : ℂ → (V →L[ℝ] V)) := by sorry
