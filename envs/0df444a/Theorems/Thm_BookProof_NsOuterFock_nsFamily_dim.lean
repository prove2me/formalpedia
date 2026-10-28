-- Prove2me | Theorems.Thm_BookProof_NsOuterFock_nsFamily_dim
-- name    : BookProof.NsOuterFock.nsFamily_dim
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:31:24.736855+00:00
-- url     : https://prove2.me/theorems/a05ee624-01a9-4334-be18-9718f464e989
-- title:
--   `BookProof.NsOuterFock.nsFamily_dim` : (nsFamily hB hbv hnu hlam hmu hgg).dim = fun n => n * 18
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsOuterFockFarisLavine`.
--
--   `BookProof.NsOuterFock.nsFamily_dim` : (nsFamily hB hbv hnu hlam hmu hgg).dim = fun n => n * 18
--
--   Formalization note: Lean 4 identifier `BookProof.NsOuterFock.nsFamily_dim`.

-- Generated from ChapterNsOuterFockFarisLavine.lean — theorem BookProof.NsOuterFock.nsFamily_dim
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

theorem BookProof.NsOuterFock.nsFamily_dim : (nsFamily hB hbv hnu hlam hmu hgg).dim = fun n => n * 18 := by sorry
