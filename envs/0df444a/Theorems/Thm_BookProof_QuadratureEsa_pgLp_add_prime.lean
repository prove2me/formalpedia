-- Prove2me | Theorems.Thm_BookProof_QuadratureEsa_pgLp_add_prime
-- name    : BookProof.QuadratureEsa.pgLp_add_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:38:51.255557+00:00
-- url     : https://prove2.me/theorems/d0b61ff0-3bfa-4305-b34d-705a1ef84943
-- title:
--   BookProof.QuadratureEsa.pgLp_add'
-- statement:
--   BookProof.QuadratureEsa.pgLp_add'

-- Generated from ChapterQuadratureEsa.lean — theorem BookProof.QuadratureEsa.pgLp_add'
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

theorem BookProof.QuadratureEsa.pgLp_add_prime (p q : MvPolynomial (Fin d) ℂ) : pgLp (p + q) = pgLp p + pgLp q := by sorry
