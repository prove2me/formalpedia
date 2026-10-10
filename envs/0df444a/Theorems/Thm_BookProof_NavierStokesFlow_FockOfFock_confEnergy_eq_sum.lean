-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_confEnergy_eq_sum
-- name    : BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:41:13.225986+00:00
-- url     : https://prove2.me/theorems/ecb708bb-5555-4308-ad85-6ecd30d642ce
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_sum` {ω : M → ℝ} {n : Conf M} {S : Finset M} (hS : n.support ⊆ S) : confEnergy ω n = ∑ m ∈ S, (n m : ℝ) * ω m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_sum` {ω : M → ℝ} {n : Conf M} {S : Finset M} (hS : n.support ⊆ S) : confEnergy ω n = ∑ m ∈ S, (n m : ℝ) * ω m
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_sum`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_sum
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

theorem BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_sum {ω : M → ℝ} {n : Conf M} {S : Finset M} (hS : n.support ⊆ S) :
    confEnergy ω n = ∑ m ∈ S, (n m : ℝ) * ω m := by sorry
