-- Prove2me | Theorems.Thm_BookProof_NsNonlinearFarisLavine_nsSquareComparison_commForm_bound
-- name    : BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:55:19.783759+00:00
-- url     : https://prove2.me/theorems/be5e2881-7623-4b26-97cd-d79d9f3fc2ad
-- title:
--   `BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm_bound` {L : ℝ} (hL : ∀ i, S.lam i ≤ L) (hL0 : 0 ≤ L) (x : polyGaussCore (d := d)) : |commForm (nsKoopmanOp S) (nsSquar
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsNonlinearFarisLavine`.
--
--   `BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm_bound` {L : ℝ} (hL : ∀ i, S.lam i ≤ L) (hL0 : 0 ≤ L) (x : polyGaussCore (d := d)) : |commForm (nsKoopmanOp S) (nsSquareComparison S) x| ≤ (2 * S.nu * L) * quadForm (nsSquareComparison S) x
--
--   Formalization note: Lean 4 identifier `BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm_bound`.

-- Generated from ChapterNsNonlinearFarisLavine.lean — theorem BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm_bound
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

theorem BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm_bound {L : ℝ} (hL : ∀ i, S.lam i ≤ L) (hL0 : 0 ≤ L)
    (x : polyGaussCore (d := d)) :
    |commForm (nsKoopmanOp S) (nsSquareComparison S) x|
      ≤ (2 * S.nu * L) * quadForm (nsSquareComparison S) x := by sorry
