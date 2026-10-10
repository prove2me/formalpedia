-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_dGamma_eq_sum_numberOp
-- name    : BookProof.NavierStokesFlow.FockOfFock.dGamma_eq_sum_numberOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:42:26.555961+00:00
-- url     : https://prove2.me/theorems/bd04f0ba-a848-4f16-a7d5-9a7b3289837d
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.dGamma_eq_sum_numberOp` (ω : M → ℝ) {n : Conf M} {S : Finset M} (hS : n.support ⊆ S) : dGamma ω (fockBasis n) = ∑ m ∈ S, ((ω m : ℝ) : ℂ) • nu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.dGamma_eq_sum_numberOp` (ω : M → ℝ) {n : Conf M} {S : Finset M} (hS : n.support ⊆ S) : dGamma ω (fockBasis n) = ∑ m ∈ S, ((ω m : ℝ) : ℂ) • numberOp m (fockBasis n)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.dGamma_eq_sum_numberOp`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.dGamma_eq_sum_numberOp
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.GhostField
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.dGamma_eq_sum_numberOp (ω : M → ℝ) {n : Conf M} {S : Finset M} (hS : n.support ⊆ S) :
    dGamma ω (fockBasis n) = ∑ m ∈ S, ((ω m : ℝ) : ℂ) • numberOp m (fockBasis n) := by sorry
