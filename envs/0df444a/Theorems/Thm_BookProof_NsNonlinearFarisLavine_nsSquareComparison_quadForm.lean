-- Prove2me | Theorems.Thm_BookProof_NsNonlinearFarisLavine_nsSquareComparison_quadForm
-- name    : BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:54:36.670226+00:00
-- url     : https://prove2.me/theorems/a926ad59-de76-4384-bb7b-f060d7d0d2de
-- title:
--   `BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm` (x : polyGaussCore (d := d)) : quadForm (nsSquareComparison S) x = ‖nsKoopmanOp S x‖ ^ 2 + quadForm (nsEnergyOp (d :=
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsNonlinearFarisLavine`.
--
--   `BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm` (x : polyGaussCore (d := d)) : quadForm (nsSquareComparison S) x = ‖nsKoopmanOp S x‖ ^ 2 + quadForm (nsEnergyOp (d := d)) x
--
--   Formalization note: Lean 4 identifier `BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm`.

-- Generated from ChapterNsNonlinearFarisLavine.lean — theorem BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterA4
import Mathlib
import Definitions.Def_ChapterNsNonlinearFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNsKoopman
open BookProof.HermiteProductCore



open MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine
open BookProof.NsKoopman

noncomputable section

variable {d : ℕ} (S : NsSystem d)

theorem BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm (x : polyGaussCore (d := d)) :
    quadForm (nsSquareComparison S) x
      = ‖nsKoopmanOp S x‖ ^ 2 + quadForm (nsEnergyOp (d := d)) x := by sorry
