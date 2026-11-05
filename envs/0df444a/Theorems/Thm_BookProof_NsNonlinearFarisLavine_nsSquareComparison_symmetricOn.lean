-- Prove2me | Theorems.Thm_BookProof_NsNonlinearFarisLavine_nsSquareComparison_symmetricOn
-- name    : BookProof.NsNonlinearFarisLavine.nsSquareComparison_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:54:15.640955+00:00
-- url     : https://prove2.me/theorems/cb9c9ae0-cea0-46cb-b5a6-70490f18a93c
-- title:
--   `BookProof.NsNonlinearFarisLavine.nsSquareComparison_symmetricOn` : SymmetricOn (polyGaussCore (d := d)) (nsSquareComparison S)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsNonlinearFarisLavine`.
--
--   `BookProof.NsNonlinearFarisLavine.nsSquareComparison_symmetricOn` : SymmetricOn (polyGaussCore (d := d)) (nsSquareComparison S)
--
--   Formalization note: Lean 4 identifier `BookProof.NsNonlinearFarisLavine.nsSquareComparison_symmetricOn`.

-- Generated from ChapterNsNonlinearFarisLavine.lean — theorem BookProof.NsNonlinearFarisLavine.nsSquareComparison_symmetricOn
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

theorem BookProof.NsNonlinearFarisLavine.nsSquareComparison_symmetricOn :
    SymmetricOn (polyGaussCore (d := d)) (nsSquareComparison S) := by sorry
