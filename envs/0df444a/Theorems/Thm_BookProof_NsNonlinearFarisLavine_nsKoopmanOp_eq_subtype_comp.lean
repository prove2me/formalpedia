-- Prove2me | Theorems.Thm_BookProof_NsNonlinearFarisLavine_nsKoopmanOp_eq_subtype_comp
-- name    : BookProof.NsNonlinearFarisLavine.nsKoopmanOp_eq_subtype_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:54:27.626801+00:00
-- url     : https://prove2.me/theorems/0e552c26-9bbd-413a-9541-fc41955a7be6
-- title:
--   `BookProof.NsNonlinearFarisLavine.nsKoopmanOp_eq_subtype_comp` : nsKoopmanOp S = (polyGaussCore (d := d)).subtype ∘ₗ nsKoopmanCore S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsNonlinearFarisLavine`.
--
--   `BookProof.NsNonlinearFarisLavine.nsKoopmanOp_eq_subtype_comp` : nsKoopmanOp S = (polyGaussCore (d := d)).subtype ∘ₗ nsKoopmanCore S
--
--   Formalization note: Lean 4 identifier `BookProof.NsNonlinearFarisLavine.nsKoopmanOp_eq_subtype_comp`.

-- Generated from ChapterNsNonlinearFarisLavine.lean — theorem BookProof.NsNonlinearFarisLavine.nsKoopmanOp_eq_subtype_comp
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterA4
import Mathlib
import Definitions.Def_ChapterNsNonlinearFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNsKoopman
open BookProof.HermiteProductCore



open MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine
open BookProof.NsKoopman

noncomputable section

variable {d : ℕ} (S : NsSystem d)

theorem BookProof.NsNonlinearFarisLavine.nsKoopmanOp_eq_subtype_comp :
    nsKoopmanOp S = (polyGaussCore (d := d)).subtype ∘ₗ nsKoopmanCore S := by sorry
