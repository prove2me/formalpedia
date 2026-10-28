-- Prove2me | Theorems.Thm_BookProof_NsOuterFock_linForm_nsGaugeY
-- name    : BookProof.NsOuterFock.linForm_nsGaugeY
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:30:13.627909+00:00
-- url     : https://prove2.me/theorems/acf19996-21be-4913-b4bd-805179e9eb73
-- title:
--   `BookProof.NsOuterFock.linForm_nsGaugeY` {n : ℕ} (p : Fin n) (j : Fin 3) (hne : nextPart p ≠ p) : linForm (nsVec bv nu lam mu gg n (p, locY j)) = ((gg : ℝ) : ℂ) • X (coordOf p (loc
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsOuterFockFarisLavine`.
--
--   `BookProof.NsOuterFock.linForm_nsGaugeY` {n : ℕ} (p : Fin n) (j : Fin 3) (hne : nextPart p ≠ p) : linForm (nsVec bv nu lam mu gg n (p, locY j)) = ((gg : ℝ) : ℂ) • X (coordOf p (locY j))
--
--   Formalization note: Lean 4 identifier `BookProof.NsOuterFock.linForm_nsGaugeY`.

-- Generated from ChapterNsOuterFockFarisLavine.lean — theorem BookProof.NsOuterFock.linForm_nsGaugeY
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

theorem BookProof.NsOuterFock.linForm_nsGaugeY {n : ℕ} (p : Fin n) (j : Fin 3) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, locY j))
      = ((gg : ℝ) : ℂ) • X (coordOf p (locY j)) := by sorry
