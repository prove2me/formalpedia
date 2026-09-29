-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_continuityHamiltonian_hasZeroDeficiencyOn_finiteModes
-- name    : BookProof.NavierStokesFlow.continuityHamiltonian_hasZeroDeficiencyOn_finiteModes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:09:39.260986+00:00
-- url     : https://prove2.me/theorems/dc8e00dc-0f35-40c1-ae58-d83b991c3480
-- title:
--   The Lean 4 theorem `continuityHamiltonian_hasZeroDeficiencyOn_finiteModes` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `continuityHamiltonian_hasZeroDeficiencyOn_finiteModes` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.continuityHamiltonian_hasZeroDeficiencyOn_finiteModes
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
import Theorems.Thm_BookProof_NavierStokesFlow_continuityHamiltonian_mem_finiteModes
import Definitions.Def_ChapterDirectSumEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite

theorem BookProof.NavierStokesFlow.continuityHamiltonian_hasZeroDeficiencyOn_finiteModes (v : LinfZ) :
    HasZeroDeficiencyOn finiteModes
      (LinearMap.codRestrict finiteModes
        ((continuityHamiltonian v : L2Z →ₗ[ℂ] L2Z).comp finiteModes.subtype)
        fun f => continuityHamiltonian_mem_finiteModes v f.2) := by sorry
