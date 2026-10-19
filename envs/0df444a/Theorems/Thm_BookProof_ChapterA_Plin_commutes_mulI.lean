-- Prove2me | Theorems.Thm_BookProof_ChapterA_Plin_commutes_mulI
-- name    : BookProof.ChapterA.Plin_commutes_mulI
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:17:23.956067+00:00
-- url     : https://prove2.me/theorems/e16f0245-799b-4e45-9a2e-26ab768e809a
-- title:
--   `BookProof.ChapterA.Plin_commutes_mulI` (S : V →L[ℝ] V) (x : V) : Plin S (Complex.I • x) = Complex.I • Plin S x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2c`.
--
--   `BookProof.ChapterA.Plin_commutes_mulI` (S : V →L[ℝ] V) (x : V) : Plin S (Complex.I • x) = Complex.I • Plin S x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.Plin_commutes_mulI`.

-- Generated from ChapterA2c.lean — theorem BookProof.ChapterA.Plin_commutes_mulI
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.Plin_commutes_mulI (S : V →L[ℝ] V) (x : V) :
    Plin S (Complex.I • x) = Complex.I • Plin S x := by sorry
