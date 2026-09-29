-- Prove2me | Theorems.Thm_BookProof_ChapterH8_compress_rational_transfer
-- name    : BookProof.ChapterH8.compress_rational_transfer
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:40:23.726343+00:00
-- url     : https://prove2.me/theorems/dbffc6ed-49a8-4776-9fd2-0fefd689ce01
-- title:
--   (V : F →L[ℂ] E) (X qX qXinv : E →L[ℂ] E) (qBinv : F →L[ℂ] F) (p : Polynomial ℂ) (hVV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F) (hinvX : ∀ x : F, ∃ y : F, X (V x) = V y) (hinvq : ∀ x : F,...
-- statement:
--   Lean 4 theorem `BookProof.ChapterH8.compress_rational_transfer` (module `BookProof.ChapterH8`), source chapter `BookProof/ChapterChapterH8.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.compress_rational_transfer
import Mathlib
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH4
open BookProof.ChapterH8 BookProof.ChapterH4
open ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in

theorem BookProof.ChapterH8.compress_rational_transfer (V : F →L[ℂ] E) (X qX qXinv : E →L[ℂ] E)
    (qBinv : F →L[ℂ] F) (p : Polynomial ℂ)
    (hVV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F)
    (hinvX : ∀ x : F, ∃ y : F, X (V x) = V y)
    (hinvq : ∀ x : F, ∃ y : F, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ F)
    (v : E) (hv : V ((adjoint V) v) = v) :
    (Polynomial.aeval X p) (qXinv v)
      = V ((Polynomial.aeval (compress V X) p) (qBinv ((adjoint V) v))) := by sorry
