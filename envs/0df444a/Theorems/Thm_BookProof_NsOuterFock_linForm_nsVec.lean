-- Prove2me | Theorems.Thm_BookProof_NsOuterFock_linForm_nsVec
-- name    : BookProof.NsOuterFock.linForm_nsVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:28:48.14304+00:00
-- url     : https://prove2.me/theorems/b8662656-5fa1-4b01-a3d0-90f058f11fa1
-- title:
--   `BookProof.NsOuterFock.linForm_nsVec` {n : ℕ} (p : Fin n) (f : NsLoc) (hne : nextPart p ≠ p) : linForm (nsVec bv nu lam mu gg n (p, f)) = (∑ l : NsLoc, ((sameVec bv nu lam mu gg f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsOuterFockFarisLavine`.
--
--   `BookProof.NsOuterFock.linForm_nsVec` {n : ℕ} (p : Fin n) (f : NsLoc) (hne : nextPart p ≠ p) : linForm (nsVec bv nu lam mu gg n (p, f)) = (∑ l : NsLoc, ((sameVec bv nu lam mu gg f l : ℝ) : ℂ) • X (coordOf p l)) + ∑ l : NsLoc, ((nextVec lam mu f l : ℝ) : ℂ) • X (coordOf (nextPart p) l)
--
--   Formalization note: Lean 4 identifier `BookProof.NsOuterFock.linForm_nsVec`.

-- Generated from ChapterNsOuterFockFarisLavine.lean — theorem BookProof.NsOuterFock.linForm_nsVec
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

theorem BookProof.NsOuterFock.linForm_nsVec {n : ℕ} (p : Fin n) (f : NsLoc) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, f))
      = (∑ l : NsLoc, ((sameVec bv nu lam mu gg f l : ℝ) : ℂ) • X (coordOf p l))
        + ∑ l : NsLoc, ((nextVec lam mu f l : ℝ) : ℂ) • X (coordOf (nextPart p) l) := by sorry
