-- Prove2me | Theorems.Thm_BookProof_QuadratureEsa_pgLp_sub_prime
-- name    : BookProof.QuadratureEsa.pgLp_sub_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:39:32.590443+00:00
-- url     : https://prove2.me/theorems/98c40baa-089b-4ffd-a87b-3a7f96914b92
-- title:
--   BookProof.QuadratureEsa.pgLp_sub'
-- statement:
--   BookProof.QuadratureEsa.pgLp_sub'

-- Generated from ChapterQuadratureEsa.lean — theorem BookProof.QuadratureEsa.pgLp_sub'
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteProductCore
open BookProof.QuadratureEsa



open MeasureTheory MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.YangMillsHermite
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

variable {d : ℕ}

theorem BookProof.QuadratureEsa.pgLp_sub_prime (p q : MvPolynomial (Fin d) ℂ) : pgLp (p - q) = pgLp p - pgLp q := by sorry
