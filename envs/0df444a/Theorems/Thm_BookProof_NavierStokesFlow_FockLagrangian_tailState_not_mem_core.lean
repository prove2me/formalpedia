-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_tailState_not_mem_core
-- name    : BookProof.NavierStokesFlow.FockLagrangian.tailState_not_mem_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T13:50:32.318633+00:00
-- url     : https://prove2.me/theorems/9b8d9bd6-f6e1-4d9c-982b-45bf703765cf
-- title:
--   `BookProof.NavierStokesFlow.FockLagrangian.tailState_not_mem_core` : tailState ∉ momFock.core
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockParcels`.
--
--   `BookProof.NavierStokesFlow.FockLagrangian.tailState_not_mem_core` : tailState ∉ momFock.core
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockLagrangian.tailState_not_mem_core`.

-- Generated from ChapterNavierStokesFockParcels.lean — theorem BookProof.NavierStokesFlow.FockLagrangian.tailState_not_mem_core
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian


open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.NavierStokesFlow.FockLagrangian.tailState_not_mem_core : tailState ∉ momFock.core := by sorry
