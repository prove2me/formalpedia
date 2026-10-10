-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_numberDensityOp_eq_sum_numberOp
-- name    : BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_eq_sum_numberOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:10:33.110445+00:00
-- url     : https://prove2.me/theorems/9500ee65-52f0-4d74-99d0-531646d7c6df
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_eq_sum_numberOp` (dens : M → Ω → ℝ) (ξ : Ω) {n : Conf M} {S : Finset M} (hS : n.support ⊆ S) : numberDensityOp dens ξ (fockBa
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_eq_sum_numberOp` (dens : M → Ω → ℝ) (ξ : Ω) {n : Conf M} {S : Finset M} (hS : n.support ⊆ S) : numberDensityOp dens ξ (fockBasis n) = ∑ m ∈ S, ((dens m ξ : ℝ) : ℂ) • numberOp m (fockBasis n)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_eq_sum_numberOp`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_eq_sum_numberOp
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.FockSecondQuantization
open BookProof.GhostField
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_eq_sum_numberOp (dens : M → Ω → ℝ) (ξ : Ω) {n : Conf M} {S : Finset M}
    (hS : n.support ⊆ S) :
    numberDensityOp dens ξ (fockBasis n)
      = ∑ m ∈ S, ((dens m ξ : ℝ) : ℂ) • numberOp m (fockBasis n) := by sorry
