-- Prove2me | Theorems.Thm_BookProof_NsOuterFock_linForm_nsConstraint
-- name    : BookProof.NsOuterFock.linForm_nsConstraint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:29:11.699289+00:00
-- url     : https://prove2.me/theorems/25403ed2-6f47-4b6d-ac13-aa2ce7d92fdb
-- title:
--   `BookProof.NsOuterFock.linForm_nsConstraint` {n : ℕ} (p : Fin n) (i : Fin 3) (hne : nextPart p ≠ p) : linForm (nsVec bv nu lam mu gg n (p, locU i)) = (∑ j : Fin 3, ((bv j : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsOuterFockFarisLavine`.
--
--   `BookProof.NsOuterFock.linForm_nsConstraint` {n : ℕ} (p : Fin n) (i : Fin 3) (hne : nextPart p ≠ p) : linForm (nsVec bv nu lam mu gg n (p, locU i)) = (∑ j : Fin 3, ((bv j : ℝ) : ℂ) • X (coordOf p (locD i j))) - ((nu : ℝ) : ℂ) • X (coordOf p (locL i))
--
--   Formalization note: Lean 4 identifier `BookProof.NsOuterFock.linForm_nsConstraint`.

-- Generated from ChapterNsOuterFockFarisLavine.lean — theorem BookProof.NsOuterFock.linForm_nsConstraint
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

theorem BookProof.NsOuterFock.linForm_nsConstraint {n : ℕ} (p : Fin n) (i : Fin 3) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, locU i))
      = (∑ j : Fin 3, ((bv j : ℝ) : ℂ) • X (coordOf p (locD i j)))
        - ((nu : ℝ) : ℂ) • X (coordOf p (locL i)) := by sorry
