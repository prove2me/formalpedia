-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_numberDensityOp_basis
-- name    : BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_basis
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:09:51.782573+00:00
-- url     : https://prove2.me/theorems/19d98bb5-3e37-42a7-b759-ca4474680c02
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_basis` (dens : M → Ω → ℝ) (ξ : Ω) (n : Conf M) : numberDensityOp dens ξ (fockBasis n) = ((confDensity dens n ξ : ℝ) : ℂ) • fo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_basis` (dens : M → Ω → ℝ) (ξ : Ω) (n : Conf M) : numberDensityOp dens ξ (fockBasis n) = ((confDensity dens n ξ : ℝ) : ℂ) • fockBasis n
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_basis`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_basis
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_basis (dens : M → Ω → ℝ) (ξ : Ω) (n : Conf M) :
    numberDensityOp dens ξ (fockBasis n) = ((confDensity dens n ξ : ℝ) : ℂ) • fockBasis n := by sorry
