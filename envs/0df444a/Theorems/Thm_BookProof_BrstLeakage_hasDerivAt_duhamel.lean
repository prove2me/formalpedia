-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_hasDerivAt_duhamel
-- name    : BookProof.BrstLeakage.hasDerivAt_duhamel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:56:40.151248+00:00
-- url     : https://prove2.me/theorems/6834d28f-2ee5-48d5-ac2c-7a681308c235
-- title:
--   `BookProof.BrstLeakage.hasDerivAt_duhamel` (X Y : E →L[ℂ] E) (t s : ℝ) (x : E) : HasDerivAt (fun u : ℝ => (exp ((t - u) • X)) ((exp (u • Y)) x)) ((exp ((t - s) • X)) ((Y - X) ((exp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.hasDerivAt_duhamel` (X Y : E →L[ℂ] E) (t s : ℝ) (x : E) : HasDerivAt (fun u : ℝ => (exp ((t - u) • X)) ((exp (u • Y)) x)) ((exp ((t - s) • X)) ((Y - X) ((exp (s • Y)) x))) s
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.hasDerivAt_duhamel`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.hasDerivAt_duhamel
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.hasDerivAt_duhamel (X Y : E →L[ℂ] E) (t s : ℝ) (x : E) :
    HasDerivAt (fun u : ℝ => (exp ((t - u) • X)) ((exp (u • Y)) x))
      ((exp ((t - s) • X)) ((Y - X) ((exp (s • Y)) x))) s := by sorry
