-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_momFock_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.FockLagrangian.momFock_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T13:49:55.137876+00:00
-- url     : https://prove2.me/theorems/f43ebc99-3276-44c0-b4de-93479377e963
-- title:
--   `BookProof.NavierStokesFlow.FockLagrangian.momFock_hasZeroDeficiencyOn` : HasZeroDeficiencyOn momFock.data.D momFock.data.hFull
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockParcels`.
--
--   `BookProof.NavierStokesFlow.FockLagrangian.momFock_hasZeroDeficiencyOn` : HasZeroDeficiencyOn momFock.data.D momFock.data.hFull
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockLagrangian.momFock_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesFockParcels.lean — theorem BookProof.NavierStokesFlow.FockLagrangian.momFock_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian


open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.NavierStokesFlow.FockLagrangian.momFock_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn momFock.data.D momFock.data.hFull := by sorry
