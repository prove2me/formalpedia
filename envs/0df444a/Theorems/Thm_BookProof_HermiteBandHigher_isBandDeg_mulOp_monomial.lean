-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_isBandDeg_mulOp_monomial
-- name    : BookProof.HermiteBandHigher.isBandDeg_mulOp_monomial
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:08:01.127309+00:00
-- url     : https://prove2.me/theorems/4ce3e45c-becf-4c31-a2ad-1ac10226f7c7
-- title:
--   `BookProof.HermiteBandHigher.isBandDeg_mulOp_monomial` (s : Fin d →₀ ℕ) (c : ℂ) : IsBandDeg s.degree (mulOp (monomial s c : MvPolynomial (Fin d) ℂ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.isBandDeg_mulOp_monomial` (s : Fin d →₀ ℕ) (c : ℂ) : IsBandDeg s.degree (mulOp (monomial s c : MvPolynomial (Fin d) ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.isBandDeg_mulOp_monomial`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.isBandDeg_mulOp_monomial
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

theorem BookProof.HermiteBandHigher.isBandDeg_mulOp_monomial (s : Fin d →₀ ℕ) (c : ℂ) :
    IsBandDeg s.degree (mulOp (monomial s c : MvPolynomial (Fin d) ℂ)) := by sorry
