-- Prove2me | Theorems.Thm_BookProof_QuadFockEsa_hermCol_apply
-- name    : BookProof.QuadFockEsa.hermCol_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T21:07:47.12459+00:00
-- url     : https://prove2.me/theorems/f5de026c-91b1-453b-9d2c-1a0d42d12e53
-- title:
--   `BookProof.QuadFockEsa.hermCol_apply` (e : ℕ ≃ (Fin d →₀ ℕ)) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (k j : ℕ) : hermCol e T k j = (inner ℂ (hermiteMvLp (e j)) (pgLp (T (hpsi (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuadraticFockEsa`.
--
--   `BookProof.QuadFockEsa.hermCol_apply` (e : ℕ ≃ (Fin d →₀ ℕ)) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (k j : ℕ) : hermCol e T k j = (inner ℂ (hermiteMvLp (e j)) (pgLp (T (hpsi (e k)))) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.QuadFockEsa.hermCol_apply`.

-- Generated from ChapterQuadraticFockEsa.lean — theorem BookProof.QuadFockEsa.hermCol_apply
import Definitions.Def_ChapterGradedBandSchurEsa
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterQuadraticFockEsa
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterQuadraticFockEsa
open BookProof.FockSecondQuantization
open BookProof.HermiteBand
open BookProof.HermiteGalerkin
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.QuadFockEsa



open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.GradedBandSchur
open BookProof.FockSecondQuantization BookProof.NavierStokesFlow
open BookProof.HermiteGalerkin BookProof.FarisLavine
open BookProof.YangMillsHermite BookProof.FullQuadratic
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadFockEsa.hermCol_apply (e : ℕ ≃ (Fin d →₀ ℕ)) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ))
    (k j : ℕ) :
    hermCol e T k j = (inner ℂ (hermiteMvLp (e j)) (pgLp (T (hpsi (e k)))) : ℂ) := by sorry
