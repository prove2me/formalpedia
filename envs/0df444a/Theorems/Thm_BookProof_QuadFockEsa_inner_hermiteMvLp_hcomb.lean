-- Prove2me | Theorems.Thm_BookProof_QuadFockEsa_inner_hermiteMvLp_hcomb
-- name    : BookProof.QuadFockEsa.inner_hermiteMvLp_hcomb
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T21:06:32.172919+00:00
-- url     : https://prove2.me/theorems/5f9a2d5b-4344-482b-a4d8-9b16e0dff741
-- title:
--   `BookProof.QuadFockEsa.inner_hermiteMvLp_hcomb` (f : (Fin d →₀ ℕ) →₀ ℂ) (β : Fin d →₀ ℕ) : (inner ℂ (hermiteMvLp β) (pgLp (hcomb f)) : ℂ) = f β
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuadraticFockEsa`.
--
--   `BookProof.QuadFockEsa.inner_hermiteMvLp_hcomb` (f : (Fin d →₀ ℕ) →₀ ℂ) (β : Fin d →₀ ℕ) : (inner ℂ (hermiteMvLp β) (pgLp (hcomb f)) : ℂ) = f β
--
--   Formalization note: Lean 4 identifier `BookProof.QuadFockEsa.inner_hermiteMvLp_hcomb`.

-- Generated from ChapterQuadraticFockEsa.lean — theorem BookProof.QuadFockEsa.inner_hermiteMvLp_hcomb
import Definitions.Def_ChapterGradedBandSchurEsa
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterQuadraticFockEsa
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterQuadraticFockEsa
open BookProof.HermiteBand
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

theorem BookProof.QuadFockEsa.inner_hermiteMvLp_hcomb (f : (Fin d →₀ ℕ) →₀ ℂ) (β : Fin d →₀ ℕ) :
    (inner ℂ (hermiteMvLp β) (pgLp (hcomb f)) : ℂ) = f β := by sorry
