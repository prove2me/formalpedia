-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_lagCan_hFull_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_hFull_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:16:39.831445+00:00
-- url     : https://prove2.me/theorems/685866c4-598a-485a-afeb-16142aac9a2f
-- title:
--   (hnu : 0 < nu) (f : Fin 3 → ℝ) : HasZeroDeficiencyOn (lagCanData nu hnu f).D (lagCanData nu hnu f).hFull
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_hFull_hasZeroDeficiencyOn` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_hFull_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.LagrangianNS














variable (nu : ℝ)

theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_hFull_hasZeroDeficiencyOn (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    HasZeroDeficiencyOn (lagCanData nu hnu f).D (lagCanData nu hnu f).hFull := by sorry
