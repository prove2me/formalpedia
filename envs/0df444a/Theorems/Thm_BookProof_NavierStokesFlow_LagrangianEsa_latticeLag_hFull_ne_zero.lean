-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_latticeLag_hFull_ne_zero
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.latticeLag_hFull_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:20:19.701977+00:00
-- url     : https://prove2.me/theorems/6f9db9bf-1a92-4c8b-86c6-6b891865f194
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.latticeLag_hFull_ne_zero` : (latticeLagData (fun _ => zeroField) zeroField (fun _ => 0) (le_refl (0 : ℝ))).hFull ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.latticeLag_hFull_ne_zero` : (latticeLagData (fun _ => zeroField) zeroField (fun _ => 0) (le_refl (0 : ℝ))).hFull ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.latticeLag_hFull_ne_zero`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.latticeLag_hFull_ne_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.NavierStokesFlow.LagrangianEsa.latticeLag_hFull_ne_zero :
    (latticeLagData (fun _ => zeroField) zeroField (fun _ => 0) (le_refl (0 : ℝ))).hFull ≠ 0 := by sorry
