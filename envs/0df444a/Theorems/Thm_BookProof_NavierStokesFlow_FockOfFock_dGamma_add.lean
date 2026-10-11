-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_dGamma_add
-- name    : BookProof.NavierStokesFlow.FockOfFock.dGamma_add
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:04:21.613915+00:00
-- url     : https://prove2.me/theorems/83d807a3-885b-48e5-949c-516d09aaefd6
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.dGamma_add` (ω₁ ω₂ : M → ℝ) : dGamma (ω₁ + ω₂) = dGamma ω₁ + dGamma ω₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.dGamma_add` (ω₁ ω₂ : M → ℝ) : dGamma (ω₁ + ω₂) = dGamma ω₁ + dGamma ω₂
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.dGamma_add`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.dGamma_add
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

theorem BookProof.NavierStokesFlow.FockOfFock.dGamma_add (ω₁ ω₂ : M → ℝ) : dGamma (ω₁ + ω₂) = dGamma ω₁ + dGamma ω₂ := by sorry
