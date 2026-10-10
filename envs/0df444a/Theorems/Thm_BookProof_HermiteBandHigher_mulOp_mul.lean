-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_mulOp_mul
-- name    : BookProof.HermiteBandHigher.mulOp_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:06:37.593996+00:00
-- url     : https://prove2.me/theorems/9797af04-b351-4de1-9234-8e936a5c5849
-- title:
--   `BookProof.HermiteBandHigher.mulOp_mul` (f g : MvPolynomial (Fin d) ℂ) : mulOp (f * g) = (mulOp f) ∘ₗ (mulOp g)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.mulOp_mul` (f g : MvPolynomial (Fin d) ℂ) : mulOp (f * g) = (mulOp f) ∘ₗ (mulOp g)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.mulOp_mul`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.mulOp_mul
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterF7
open BookProof.ChapterF7
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

theorem BookProof.HermiteBandHigher.mulOp_mul (f g : MvPolynomial (Fin d) ℂ) :
    mulOp (f * g) = (mulOp f) ∘ₗ (mulOp g) := by sorry
