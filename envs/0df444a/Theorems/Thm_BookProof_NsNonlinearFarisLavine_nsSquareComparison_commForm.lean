-- Prove2me | Theorems.Thm_BookProof_NsNonlinearFarisLavine_nsSquareComparison_commForm
-- name    : BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:55:41.884998+00:00
-- url     : https://prove2.me/theorems/65113319-f2a5-416f-915d-e79ff358413e
-- title:
--   `BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm` (x : polyGaussCore (d := d)) : commForm (nsKoopmanOp S) (nsSquareComparison S) x = (gpair ((coreRepPoly d).equiv.symm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsNonlinearFarisLavine`.
--
--   `BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm` (x : polyGaussCore (d := d)) : commForm (nsKoopmanOp S) (nsSquareComparison S) x = (gpair ((coreRepPoly d).equiv.symm x) (fluxPoly S * (coreRepPoly d).equiv.symm x)).re
--
--   Formalization note: Lean 4 identifier `BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm`.

-- Generated from ChapterNsNonlinearFarisLavine.lean — theorem BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterA4
import Mathlib
import Definitions.Def_ChapterNsNonlinearFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterNsKoopman
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite



open MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine
open BookProof.NsKoopman

noncomputable section

variable {d : ℕ} (S : NsSystem d)

theorem BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm (x : polyGaussCore (d := d)) :
    commForm (nsKoopmanOp S) (nsSquareComparison S) x
      = (gpair ((coreRepPoly d).equiv.symm x)
          (fluxPoly S * (coreRepPoly d).equiv.symm x)).re := by sorry
