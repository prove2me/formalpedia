-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_linearFull_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.Carleman.linearFull_hasZeroDeficiencyOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:37:45.243798+00:00
-- url     : https://prove2.me/theorems/f3075b0c-df36-4a01-993c-f5e474b22584
-- title:
--   `BookProof.NavierStokesFlow.Carleman.linearFull_hasZeroDeficiencyOn` : HasZeroDeficiencyOn linearFullData.D linearFullData.hamiltonian
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.linearFull_hasZeroDeficiencyOn` : HasZeroDeficiencyOn linearFullData.D linearFullData.hamiltonian
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.linearFull_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.linearFull_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.linearFull_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn linearFullData.D linearFullData.hamiltonian := by sorry
