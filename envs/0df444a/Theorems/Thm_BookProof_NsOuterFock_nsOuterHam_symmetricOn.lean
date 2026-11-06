-- Prove2me | Theorems.Thm_BookProof_NsOuterFock_nsOuterHam_symmetricOn
-- name    : BookProof.NsOuterFock.nsOuterHam_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:55:02.221119+00:00
-- url     : https://prove2.me/theorems/c4d9799a-2bd1-4737-bc0f-165a6807cecf
-- title:
--   `BookProof.NsOuterFock.nsOuterHam_symmetricOn` : SymmetricOn (outerCore (nsFamily hB hbv hnu hlam hmu hgg).dim) (nsFamily hB hbv hnu hlam hmu hgg).outerHam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsOuterFockFarisLavine`.
--
--   `BookProof.NsOuterFock.nsOuterHam_symmetricOn` : SymmetricOn (outerCore (nsFamily hB hbv hnu hlam hmu hgg).dim) (nsFamily hB hbv hnu hlam hmu hgg).outerHam
--
--   Formalization note: Lean 4 identifier `BookProof.NsOuterFock.nsOuterHam_symmetricOn`.

-- Generated from ChapterNsOuterFockFarisLavine.lean — theorem BookProof.NsOuterFock.nsOuterHam_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterSqSumOuterFamily
import Mathlib
import Definitions.Def_ChapterNsOuterFockFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductCore



open Finset MvPolynomial
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL
open BookProof.SqSumOuterFamily

noncomputable section

variable (bv : Fin 3 → ℝ) (nu lam mu gg : ℝ)
variable {bv nu lam mu gg}
variable {B : ℝ} (hB : 0 ≤ B) (hbv : ∀ j, |bv j| ≤ B) (hnu : |nu| ≤ B) (hlam : |lam| ≤ B)
  (hmu : |mu| ≤ B) (hgg : |gg| ≤ B)

theorem BookProof.NsOuterFock.nsOuterHam_symmetricOn :
    SymmetricOn (outerCore (nsFamily hB hbv hnu hlam hmu hgg).dim)
      (nsFamily hB hbv hnu hlam hmu hgg).outerHam := by sorry
