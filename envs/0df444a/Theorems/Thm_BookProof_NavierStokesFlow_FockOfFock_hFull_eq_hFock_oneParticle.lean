-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_hFull_eq_hFock_oneParticle
-- name    : BookProof.NavierStokesFlow.FockOfFock.hFull_eq_hFock_oneParticle
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:11:57.139547+00:00
-- url     : https://prove2.me/theorems/b4bc4940-0ec5-4859-9521-3e23fbd6274c
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.hFull_eq_hFock_oneParticle` (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ) (m : M) : (lagrangianFockData
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.hFull_eq_hFock_oneParticle` (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ) (m : M) : (lagrangianFockData nu hnu p q dr force cst).hFull (fockBasis (Finsupp.single m 1)) = hFockLag nu p q dr force cst (fockBasis (Finsupp.single m 1))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.hFull_eq_hFock_oneParticle`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.hFull_eq_hFock_oneParticle
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.BRSTNilpotent
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]

theorem BookProof.NavierStokesFlow.FockOfFock.hFull_eq_hFock_oneParticle (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ)
    (force : Fin 3 → ℝ) (cst : M → ℝ) (m : M) :
    (lagrangianFockData nu hnu p q dr force cst).hFull (fockBasis (Finsupp.single m 1))
      = hFockLag nu p q dr force cst (fockBasis (Finsupp.single m 1)) := by sorry
