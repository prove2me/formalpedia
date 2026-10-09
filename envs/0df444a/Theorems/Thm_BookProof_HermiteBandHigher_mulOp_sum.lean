-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_mulOp_sum
-- name    : BookProof.HermiteBandHigher.mulOp_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:07:56.704849+00:00
-- url     : https://prove2.me/theorems/1d4e96e5-fad7-4485-8050-7f71b120f068
-- title:
--   `BookProof.HermiteBandHigher.mulOp_sum` {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin d) ℂ) : mulOp (∑ i ∈ s, F i) = ∑ i ∈ s, mulOp (F i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.mulOp_sum` {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin d) ℂ) : mulOp (∑ i ∈ s, F i) = ∑ i ∈ s, mulOp (F i)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.mulOp_sum`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.mulOp_sum
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

theorem BookProof.HermiteBandHigher.mulOp_sum {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin d) ℂ) :
    mulOp (∑ i ∈ s, F i) = ∑ i ∈ s, mulOp (F i) := by sorry
