-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_hFull_eigenvector
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_eigenvector
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:54:19.29651+00:00
-- url     : https://prove2.me/theorems/faa422eb-e316-4ff8-a4c7-7d6786c2a254
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_eigenvector` {v : L.D} {p q dr : Fin 3 → ℝ} {c : ℝ} (hP : ∀ i, L.P i v = ((p i : ℝ) : ℂ) • v) (hQ : ∀ i, L.Q i v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_eigenvector` {v : L.D} {p q dr : Fin 3 → ℝ} {c : ℝ} (hP : ∀ i, L.P i v = ((p i : ℝ) : ℂ) • v) (hQ : ∀ i, L.Q i v = ((q i : ℝ) : ℂ) • v) (hD : ∀ i, L.drive i v = ((dr i : ℝ) : ℂ) • v) (hC : L.constraintOp v = ((c : ℝ) : ℂ) • v) : L.hFull v = ((L.eigenvalue p q dr c : ℝ) : ℂ) • v
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_eigenvector`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_eigenvector
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

theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_eigenvector {v : L.D} {p q dr : Fin 3 → ℝ} {c : ℝ}
    (hP : ∀ i, L.P i v = ((p i : ℝ) : ℂ) • v) (hQ : ∀ i, L.Q i v = ((q i : ℝ) : ℂ) • v)
    (hD : ∀ i, L.drive i v = ((dr i : ℝ) : ℂ) • v)
    (hC : L.constraintOp v = ((c : ℝ) : ℂ) • v) :
    L.hFull v = ((L.eigenvalue p q dr c : ℝ) : ℂ) • v := by sorry
