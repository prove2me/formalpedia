-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_hasZeroDeficiencyOn_of_commonEigenvectors
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T12:23:01.238862+00:00
-- url     : https://prove2.me/theorems/54e6e83b-9a6d-47a3-a12c-2e7951dbfa01
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors` {I : Type*} (e : I → L.D) (p q dr : Fin 3 → I → ℝ) (c : I → ℝ) (hP : ∀ i a,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors` {I : Type*} (e : I → L.D) (p q dr : Fin 3 → I → ℝ) (c : I → ℝ) (hP : ∀ i a, L.P i (e a) = ((p i a : ℝ) : ℂ) • e a) (hQ : ∀ i a, L.Q i (e a) = ((q i a : ℝ) : ℂ) • e a) (hD : ∀ i a, L.drive i (e a) = ((dr i a : ℝ) : ℂ) • e a) (hC : ∀ a, L.constraintOp (e a) = ((c a : ℝ) : ℂ) • e a) (htotal : ∀ w : F, (∀ a, (inner ℂ ((e a : F)) w : ℂ) = 0) → w = 0) : HasZeroDeficiencyOn L.D L.hFull
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.BRSTNilpotent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors {I : Type*} (e : I → L.D)
    (p q dr : Fin 3 → I → ℝ) (c : I → ℝ)
    (hP : ∀ i a, L.P i (e a) = ((p i a : ℝ) : ℂ) • e a)
    (hQ : ∀ i a, L.Q i (e a) = ((q i a : ℝ) : ℂ) • e a)
    (hD : ∀ i a, L.drive i (e a) = ((dr i a : ℝ) : ℂ) • e a)
    (hC : ∀ a, L.constraintOp (e a) = ((c a : ℝ) : ℂ) • e a)
    (htotal : ∀ w : F, (∀ a, (inner ℂ ((e a : F)) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn L.D L.hFull := by sorry
