-- Prove2me | Theorems.Thm_BookProof_NsOuterFock_nsVec_coupling
-- name    : BookProof.NsOuterFock.nsVec_coupling
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:27:52.824775+00:00
-- url     : https://prove2.me/theorems/5faa7c1c-afbf-4d76-9c60-27c091f8f3b2
-- title:
--   `BookProof.NsOuterFock.nsVec_coupling` {n : ℕ} (p : Fin n) (i j : Fin 3) (hne : nextPart p ≠ p) : nsVec bv nu lam mu gg n (p, locD i j) (coordOf (nextPart p) (locU i)) = -lam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsOuterFockFarisLavine`.
--
--   `BookProof.NsOuterFock.nsVec_coupling` {n : ℕ} (p : Fin n) (i j : Fin 3) (hne : nextPart p ≠ p) : nsVec bv nu lam mu gg n (p, locD i j) (coordOf (nextPart p) (locU i)) = -lam
--
--   Formalization note: Lean 4 identifier `BookProof.NsOuterFock.nsVec_coupling`.

-- Generated from ChapterNsOuterFockFarisLavine.lean — theorem BookProof.NsOuterFock.nsVec_coupling
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterSqSumOuterFamily
import Mathlib
import Definitions.Def_ChapterNsOuterFockFarisLavine
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterShiftedQuadraticEsa



open Finset MvPolynomial
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL

noncomputable section

variable (bv : Fin 3 → ℝ) (nu lam mu gg : ℝ)

theorem BookProof.NsOuterFock.nsVec_coupling {n : ℕ} (p : Fin n) (i j : Fin 3) (hne : nextPart p ≠ p) :
    nsVec bv nu lam mu gg n (p, locD i j) (coordOf (nextPart p) (locU i)) = -lam := by sorry
