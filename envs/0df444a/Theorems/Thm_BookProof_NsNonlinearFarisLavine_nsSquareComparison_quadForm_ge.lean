-- Prove2me | Theorems.Thm_BookProof_NsNonlinearFarisLavine_nsSquareComparison_quadForm_ge
-- name    : BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:54:51.414763+00:00
-- url     : https://prove2.me/theorems/e6d0befd-0817-4f02-b119-44214507e5ec
-- title:
--   `BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_ge` (x : polyGaussCore (d := d)) : ‖(x : L2d d)‖ ^ 2 ≤ quadForm (nsSquareComparison S) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsNonlinearFarisLavine`.
--
--   `BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_ge` (x : polyGaussCore (d := d)) : ‖(x : L2d d)‖ ^ 2 ≤ quadForm (nsSquareComparison S) x
--
--   Formalization note: Lean 4 identifier `BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_ge`.

-- Generated from ChapterNsNonlinearFarisLavine.lean — theorem BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_ge
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

theorem BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_ge (x : polyGaussCore (d := d)) :
    ‖(x : L2d d)‖ ^ 2 ≤ quadForm (nsSquareComparison S) x := by sorry
