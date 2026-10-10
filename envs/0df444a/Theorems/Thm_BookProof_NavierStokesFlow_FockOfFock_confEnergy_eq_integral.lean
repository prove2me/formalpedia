-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_confEnergy_eq_integral
-- name    : BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_integral
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:43:07.944138+00:00
-- url     : https://prove2.me/theorems/210f64d5-00bf-4bd0-b1cd-2292b68b6d13
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_integral` (μ : Measure Ω) (w : Ω → ℝ) (dens : M → Ω → ℝ) (hint : ∀ m, Integrable (fun ξ => w ξ * dens m ξ) μ) (n : Conf M) : co
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_integral` (μ : Measure Ω) (w : Ω → ℝ) (dens : M → Ω → ℝ) (hint : ∀ m, Integrable (fun ξ => w ξ * dens m ξ) μ) (n : Conf M) : confEnergy (symbolOfIntegral μ w dens) n = ∫ ξ, w ξ * confDensity dens n ξ ∂μ
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_integral`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_integral
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_integral (μ : Measure Ω) (w : Ω → ℝ) (dens : M → Ω → ℝ)
    (hint : ∀ m, Integrable (fun ξ => w ξ * dens m ξ) μ) (n : Conf M) :
    confEnergy (symbolOfIntegral μ w dens) n = ∫ ξ, w ξ * confDensity dens n ξ ∂μ := by sorry
