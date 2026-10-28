-- Prove2me | Theorems.Thm_BookProof_NsOuterFock_linForm_nsLap
-- name    : BookProof.NsOuterFock.linForm_nsLap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:29:49.949737+00:00
-- url     : https://prove2.me/theorems/a4994ffe-46d1-46a0-b594-38f18f7beaba
-- title:
--   `BookProof.NsOuterFock.linForm_nsLap` {n : ℕ} (p : Fin n) (i : Fin 3) (hne : nextPart p ≠ p) : linForm (nsVec bv nu lam mu gg n (p, locL i)) = ((mu : ℝ) : ℂ) • (X (coordOf p (locL
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsOuterFockFarisLavine`.
--
--   `BookProof.NsOuterFock.linForm_nsLap` {n : ℕ} (p : Fin n) (i : Fin 3) (hne : nextPart p ≠ p) : linForm (nsVec bv nu lam mu gg n (p, locL i)) = ((mu : ℝ) : ℂ) • (X (coordOf p (locL i)) + (∑ j : Fin 3, X (coordOf p (locD i j))) - ∑ j : Fin 3, X (coordOf (nextPart p) (locD i j)))
--
--   Formalization note: Lean 4 identifier `BookProof.NsOuterFock.linForm_nsLap`.

-- Generated from ChapterNsOuterFockFarisLavine.lean — theorem BookProof.NsOuterFock.linForm_nsLap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterSqSumOuterFamily
import Mathlib
import Definitions.Def_ChapterNsOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL
open BookProof.QgOuterFock



open Finset MvPolynomial
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL

noncomputable section

variable (bv : Fin 3 → ℝ) (nu lam mu gg : ℝ)

theorem BookProof.NsOuterFock.linForm_nsLap {n : ℕ} (p : Fin n) (i : Fin 3) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, locL i))
      = ((mu : ℝ) : ℂ) • (X (coordOf p (locL i)) + (∑ j : Fin 3, X (coordOf p (locD i j)))
          - ∑ j : Fin 3, X (coordOf (nextPart p) (locD i j))) := by sorry
