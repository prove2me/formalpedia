-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_lagCan_esa
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:16:29.472231+00:00
-- url     : https://prove2.me/theorems/b730f7d2-c8ce-4b32-83a0-3e80080280f9
-- title:
--   (hnu : 0 < nu) (f : Fin 3 → ℝ) : EssentiallySelfAdjointOn (lagCanData nu hnu f).D (lagrangianCore (lagCanData nu hnu f))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_esa` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_esa
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.LagrangianKatoRellich














variable (nu : ℝ)

theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_esa (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (lagCanData nu hnu f).D (lagrangianCore (lagCanData nu hnu f)) := by sorry
