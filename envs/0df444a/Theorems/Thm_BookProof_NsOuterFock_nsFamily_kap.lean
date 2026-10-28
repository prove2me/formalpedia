-- Prove2me | Theorems.Thm_BookProof_NsOuterFock_nsFamily_kap
-- name    : BookProof.NsOuterFock.nsFamily_kap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:30:49.299258+00:00
-- url     : https://prove2.me/theorems/a4ff1b22-cd52-45b3-9cf7-effd0c1121d2
-- title:
--   `BookProof.NsOuterFock.nsFamily_kap` (n : ℕ) (I : Fin ((nsFamily hB hbv hnu hlam hmu hgg).dim n)) : (nsFamily hB hbv hnu hlam hmu hgg).kap n I = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsOuterFockFarisLavine`.
--
--   `BookProof.NsOuterFock.nsFamily_kap` (n : ℕ) (I : Fin ((nsFamily hB hbv hnu hlam hmu hgg).dim n)) : (nsFamily hB hbv hnu hlam hmu hgg).kap n I = 1
--
--   Formalization note: Lean 4 identifier `BookProof.NsOuterFock.nsFamily_kap`.

-- Generated from ChapterNsOuterFockFarisLavine.lean — theorem BookProof.NsOuterFock.nsFamily_kap
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
variable {bv nu lam mu gg}
variable {B : ℝ} (hB : 0 ≤ B) (hbv : ∀ j, |bv j| ≤ B) (hnu : |nu| ≤ B) (hlam : |lam| ≤ B)
  (hmu : |mu| ≤ B) (hgg : |gg| ≤ B)

theorem BookProof.NsOuterFock.nsFamily_kap (n : ℕ) (I : Fin ((nsFamily hB hbv hnu hlam hmu hgg).dim n)) :
    (nsFamily hB hbv hnu hlam hmu hgg).kap n I = 1 := by sorry
