-- Prove2me | Theorems.Thm_BookProof_NsNonlinearFarisLavine_nsKoopman_esa_of_squareComparison_esa
-- name    : BookProof.NsNonlinearFarisLavine.nsKoopman_esa_of_squareComparison_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:54:14.389916+00:00
-- url     : https://prove2.me/theorems/941571cd-ca53-44ff-ad74-b0dee80c5546
-- title:
--   `BookProof.NsNonlinearFarisLavine.nsKoopman_esa_of_squareComparison_esa` (hN : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (nsSquareComparison S)) : EssentiallySelfAdjointOn
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsNonlinearFarisLavine`.
--
--   `BookProof.NsNonlinearFarisLavine.nsKoopman_esa_of_squareComparison_esa` (hN : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (nsSquareComparison S)) : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (nsKoopmanOp S)
--
--   Formalization note: Lean 4 identifier `BookProof.NsNonlinearFarisLavine.nsKoopman_esa_of_squareComparison_esa`.

-- Generated from ChapterNsNonlinearFarisLavine.lean — theorem BookProof.NsNonlinearFarisLavine.nsKoopman_esa_of_squareComparison_esa
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

theorem BookProof.NsNonlinearFarisLavine.nsKoopman_esa_of_squareComparison_esa
    (hN : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (nsSquareComparison S)) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (nsKoopmanOp S) := by sorry
