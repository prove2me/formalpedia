-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_spectrum_subsingleton_of_irreducible
-- name    : BookProof.ChapterSchurIrreducible.spectrum_subsingleton_of_irreducible
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:01:31.444131+00:00
-- url     : https://prove2.me/theorems/e27efc39-6663-457a-ab33-2f2da6d0f26e
-- title:
--   `BookProof.ChapterSchurIrreducible.spectrum_subsingleton_of_irreducible` [Nontrivial V] (M : System ℂ V) (hirr : M.IsIrreducible) {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) (hcomm : M.
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.spectrum_subsingleton_of_irreducible` [Nontrivial V] (M : System ℂ V) (hirr : M.IsIrreducible) {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) (hcomm : M.Commutes T) {a b : ℝ} (ha : a ∈ spectrum ℝ T) (hb : b ∈ spectrum ℝ T) : a = b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.spectrum_subsingleton_of_irreducible`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.spectrum_subsingleton_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.spectrum_subsingleton_of_irreducible [Nontrivial V] (M : System ℂ V)
    (hirr : M.IsIrreducible) {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) (hcomm : M.Commutes T)
    {a b : ℝ} (ha : a ∈ spectrum ℝ T) (hb : b ∈ spectrum ℝ T) : a = b := by sorry
