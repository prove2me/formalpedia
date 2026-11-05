-- Prove2me | Theorems.Thm_BookProof_NsNonlinearFarisLavine_nsSquareComparison_quadForm_nonneg
-- name    : BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:54:01.52728+00:00
-- url     : https://prove2.me/theorems/30163b1d-0999-4aaa-94a7-18b008e24689
-- title:
--   `BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_nonneg` (x : polyGaussCore (d := d)) : 0 ≤ quadForm (nsSquareComparison S) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsNonlinearFarisLavine`.
--
--   `BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_nonneg` (x : polyGaussCore (d := d)) : 0 ≤ quadForm (nsSquareComparison S) x
--
--   Formalization note: Lean 4 identifier `BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_nonneg`.

-- Generated from ChapterNsNonlinearFarisLavine.lean — theorem BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_nonneg
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

theorem BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_nonneg (x : polyGaussCore (d := d)) :
    0 ≤ quadForm (nsSquareComparison S) x := by sorry
