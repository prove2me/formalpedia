-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianEsa_weylProd_self_apply
-- name    : BookProof.YangMillsAbelianEsa.weylProd_self_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:19:46.707726+00:00
-- url     : https://prove2.me/theorems/7cb8ea69-2684-4bd7-abe1-5b18672432b7
-- title:
--   `BookProof.YangMillsAbelianEsa.weylProd_self_apply` {d : ℕ} (S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) (p : MvPolynomial (Fin d) ℂ) : weylProd S S p = S (S p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianEsa`.
--
--   `BookProof.YangMillsAbelianEsa.weylProd_self_apply` {d : ℕ} (S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) (p : MvPolynomial (Fin d) ℂ) : weylProd S S p = S (S p)
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianEsa.weylProd_self_apply`.

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.weylProd_self_apply
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite
open BookProof.YangMillsAbelianEsa



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

theorem BookProof.YangMillsAbelianEsa.weylProd_self_apply {d : ℕ} (S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) : weylProd S S p = S (S p) := by sorry
