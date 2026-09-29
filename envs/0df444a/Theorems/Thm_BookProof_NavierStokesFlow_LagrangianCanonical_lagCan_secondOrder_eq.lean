-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_lagCan_secondOrder_eq
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_secondOrder_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:16:34.816399+00:00
-- url     : https://prove2.me/theorems/2165cbee-51fe-46d7-b5a3-f5a415e6889d
-- title:
--   (hnu : 0 < nu) (f : Fin 3 → ℝ) : secondOrder (lagCanData nu hnu f) = lagT nu
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_secondOrder_eq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_secondOrder_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.LagrangianKatoRellich














variable (nu : ℝ)

theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_secondOrder_eq (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    secondOrder (lagCanData nu hnu f) = lagT nu := by sorry
