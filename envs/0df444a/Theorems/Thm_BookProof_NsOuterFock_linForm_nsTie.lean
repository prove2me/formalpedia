-- Prove2me | Theorems.Thm_BookProof_NsOuterFock_linForm_nsTie
-- name    : BookProof.NsOuterFock.linForm_nsTie
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:29:42.503131+00:00
-- url     : https://prove2.me/theorems/65d27c4b-5e0c-4b1d-a1c1-9497ff0037f7
-- title:
--   `BookProof.NsOuterFock.linForm_nsTie` {n : ℕ} (p : Fin n) (i j : Fin 3) (hne : nextPart p ≠ p) : linForm (nsVec bv nu lam mu gg n (p, locD i j)) = ((lam : ℝ) : ℂ) • (X (coordOf p (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsOuterFockFarisLavine`.
--
--   `BookProof.NsOuterFock.linForm_nsTie` {n : ℕ} (p : Fin n) (i j : Fin 3) (hne : nextPart p ≠ p) : linForm (nsVec bv nu lam mu gg n (p, locD i j)) = ((lam : ℝ) : ℂ) • (X (coordOf p (locD i j)) + X (coordOf p (locU i)) - X (coordOf (nextPart p) (locU i)))
--
--   Formalization note: Lean 4 identifier `BookProof.NsOuterFock.linForm_nsTie`.

-- Generated from ChapterNsOuterFockFarisLavine.lean — theorem BookProof.NsOuterFock.linForm_nsTie
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

theorem BookProof.NsOuterFock.linForm_nsTie {n : ℕ} (p : Fin n) (i j : Fin 3) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, locD i j))
      = ((lam : ℝ) : ℂ) • (X (coordOf p (locD i j)) + X (coordOf p (locU i))
          - X (coordOf (nextPart p) (locU i))) := by sorry
