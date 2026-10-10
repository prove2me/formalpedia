-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_dGamma_inner_eq_integral
-- name    : BookProof.NavierStokesFlow.FockOfFock.dGamma_inner_eq_integral
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:10:59.660425+00:00
-- url     : https://prove2.me/theorems/23b2c217-42d3-4e16-8dbc-fd15e0fc64dc
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.dGamma_inner_eq_integral` (μ : Measure Ω) (w : Ω → ℝ) (dens : M → Ω → ℝ) (hint : ∀ m, Integrable (fun ξ => w ξ * dens m ξ) μ) (v : FockDom M)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.dGamma_inner_eq_integral` (μ : Measure Ω) (w : Ω → ℝ) (dens : M → Ω → ℝ) (hint : ∀ m, Integrable (fun ξ => w ξ * dens m ξ) μ) (v : FockDom M) : (inner ℂ ((v : FockL2 M)) ((dGamma (symbolOfIntegral μ w dens) v : FockDom M) : FockL2 M) : ℂ).re = ∫ ξ, w ξ * (inner ℂ ((v : FockL2 M)) ((numberDensityOp dens ξ v : FockDom M) : FockL2 M) : ℂ).re ∂μ
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.dGamma_inner_eq_integral`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.dGamma_inner_eq_integral
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.NavierStokesFlow.FockOfFock.dGamma_inner_eq_integral (μ : Measure Ω) (w : Ω → ℝ) (dens : M → Ω → ℝ)
    (hint : ∀ m, Integrable (fun ξ => w ξ * dens m ξ) μ) (v : FockDom M) :
    (inner ℂ ((v : FockL2 M)) ((dGamma (symbolOfIntegral μ w dens) v : FockDom M) : FockL2 M)
        : ℂ).re
      = ∫ ξ, w ξ * (inner ℂ ((v : FockL2 M))
          ((numberDensityOp dens ξ v : FockDom M) : FockL2 M) : ℂ).re ∂μ := by sorry
