-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_intervalTwoLevel_inner_eq_integral
-- name    : BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_inner_eq_integral
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:23:26.648981+00:00
-- url     : https://prove2.me/theorems/7edc158e-1f31-4ce1-91ea-863801f7766b
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_inner_eq_integral` (eps : K → ℝ) (v : FockOfFockDom ℕ K) : (inner ℂ ((v : FockOfFockL2 ℕ K)) ((dGamma (intervalTwoLevelSymbo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_inner_eq_integral` (eps : K → ℝ) (v : FockOfFockDom ℕ K) : (inner ℂ ((v : FockOfFockL2 ℕ K)) ((dGamma (intervalTwoLevelSymbol eps) v : FockOfFockDom ℕ K) : FockOfFockL2 ℕ K) : ℂ).re = (∫ ξ, extField ξ * (inner ℂ ((v : FockOfFockL2 ℕ K)) ((numberDensityOp parcelDens ξ v : FockOfFockDom ℕ K) : FockOfFockL2 ℕ K) : ℂ).re) + (inner ℂ ((v : FockOfFockL2 ℕ K)) ((dGamma (innerEnergySymbol eps) v : FockOfFockDom ℕ K) : FockOfFockL2 ℕ K) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_inner_eq_integral`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_inner_eq_integral
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
variable {J K : Type*} [DecidableEq J] [DecidableEq K]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {K : Type*} [DecidableEq K]

theorem BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_inner_eq_integral (eps : K → ℝ) (v : FockOfFockDom ℕ K) :
    (inner ℂ ((v : FockOfFockL2 ℕ K))
        ((dGamma (intervalTwoLevelSymbol eps) v : FockOfFockDom ℕ K) : FockOfFockL2 ℕ K) : ℂ).re
      = (∫ ξ, extField ξ * (inner ℂ ((v : FockOfFockL2 ℕ K))
            ((numberDensityOp parcelDens ξ v : FockOfFockDom ℕ K) : FockOfFockL2 ℕ K) : ℂ).re)
        + (inner ℂ ((v : FockOfFockL2 ℕ K))
            ((dGamma (innerEnergySymbol eps) v : FockOfFockDom ℕ K) : FockOfFockL2 ℕ K)
              : ℂ).re := by sorry
