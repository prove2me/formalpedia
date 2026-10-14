-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_latticeLagData_hFull_apply
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.latticeLagData_hFull_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:20:17.720993+00:00
-- url     : https://prove2.me/theorems/9dfcee39-bfe2-4c76-86f7-9e7cbac04586
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.latticeLagData_hFull_apply` (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) {nu : ℝ} (hnu : 0 ≤ nu) (x : (latticeLagData v w fr hnu).D) :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.latticeLagData_hFull_apply` (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) {nu : ℝ} (hnu : 0 ≤ nu) (x : (latticeLagData v w fr hnu).D) : ((latticeLagData v w fr hnu).hFull x : L2Z) = latticeLagCLM v w fr nu (x : L2Z)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.latticeLagData_hFull_apply`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.latticeLagData_hFull_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.NavierStokesFlow.LagrangianEsa.latticeLagData_hFull_apply (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) {nu : ℝ}
    (hnu : 0 ≤ nu) (x : (latticeLagData v w fr hnu).D) :
    ((latticeLagData v w fr hnu).hFull x : L2Z) = latticeLagCLM v w fr nu (x : L2Z) := by sorry
