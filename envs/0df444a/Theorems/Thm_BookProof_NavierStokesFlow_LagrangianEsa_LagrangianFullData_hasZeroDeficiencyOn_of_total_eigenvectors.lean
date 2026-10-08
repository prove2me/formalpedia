-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_hasZeroDeficiencyOn_of_total_eigenvectors
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_total_eigenvectors
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:53:42.944245+00:00
-- url     : https://prove2.me/theorems/cf4ef244-3a59-4211-ba03-087140d12659
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_total_eigenvectors` {I : Type*} (e : I → L.D) (lam : I → ℝ) (heig : ∀ a, L.hFull (e a) = ((lam a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_total_eigenvectors` {I : Type*} (e : I → L.D) (lam : I → ℝ) (heig : ∀ a, L.hFull (e a) = ((lam a : ℝ) : ℂ) • e a) (htotal : ∀ w : F, (∀ a, (inner ℂ ((e a : F)) w : ℂ) = 0) → w = 0) : HasZeroDeficiencyOn L.D L.hFull
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_total_eigenvectors`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_total_eigenvectors
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_total_eigenvectors {I : Type*} (e : I → L.D) (lam : I → ℝ)
    (heig : ∀ a, L.hFull (e a) = ((lam a : ℝ) : ℂ) • e a)
    (htotal : ∀ w : F, (∀ a, (inner ℂ ((e a : F)) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn L.D L.hFull := by sorry
