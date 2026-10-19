-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_bigState_mem_core
-- name    : BookProof.NavierStokesFlow.FockLagrangian.bigState_mem_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T13:49:13.919756+00:00
-- url     : https://prove2.me/theorems/71784453-78c6-4d17-a405-d26a4a55c6f0
-- title:
--   `BookProof.NavierStokesFlow.FockLagrangian.bigState_mem_core` {K : ℝ} (hK : 0 ≤ K) : bigState K ∈ momFock.core
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockParcels`.
--
--   `BookProof.NavierStokesFlow.FockLagrangian.bigState_mem_core` {K : ℝ} (hK : 0 ≤ K) : bigState K ∈ momFock.core
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockLagrangian.bigState_mem_core`.

-- Generated from ChapterNavierStokesFockParcels.lean — theorem BookProof.NavierStokesFlow.FockLagrangian.bigState_mem_core
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian


open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.NavierStokesFlow.FockLagrangian.bigState_mem_core {K : ℝ} (hK : 0 ≤ K) : bigState K ∈ momFock.core := by sorry
