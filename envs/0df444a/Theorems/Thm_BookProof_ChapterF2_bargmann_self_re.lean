-- Prove2me | Theorems.Thm_BookProof_ChapterF2_bargmann_self_re
-- name    : BookProof.ChapterF2.bargmann_self_re
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:47:02.462456+00:00
-- url     : https://prove2.me/theorems/91ec4316-486b-44ef-908e-ae36e7a026b4
-- title:
--   `BookProof.ChapterF2.bargmann_self_re` (p : ℂ[X]) : (bargmann p p).re = ∑ n ∈ p.support, (n.factorial : ℝ) * Complex.normSq (p.coeff n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF2`.
--
--   `BookProof.ChapterF2.bargmann_self_re` (p : ℂ[X]) : (bargmann p p).re = ∑ n ∈ p.support, (n.factorial : ℝ) * Complex.normSq (p.coeff n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF2.bargmann_self_re`.

-- Generated from ChapterF2.lean — theorem BookProof.ChapterF2.bargmann_self_re
import Definitions.Def_ChapterF1
import Mathlib
import Definitions.Def_ChapterF2
open BookProof.ChapterF2


open Polynomial Finset
open scoped BigOperators


open BookProof.ChapterF1

noncomputable section

theorem BookProof.ChapterF2.bargmann_self_re (p : ℂ[X]) :
    (bargmann p p).re = ∑ n ∈ p.support, (n.factorial : ℝ) * Complex.normSq (p.coeff n) := by sorry
