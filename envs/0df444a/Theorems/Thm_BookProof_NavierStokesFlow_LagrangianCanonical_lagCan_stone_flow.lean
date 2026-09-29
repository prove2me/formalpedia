-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_lagCan_stone_flow
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_stone_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T10:02:36.000196+00:00
-- url     : https://prove2.me/theorems/958e4cc2-ef52-4cdb-ba71-017eec1d93ec
-- title:
--   (hnu : 0 < nu) (f : Fin 3 → ℝ) : ∃ (T : UnboundedSelfAdjoint (L2I Vel)) (U : ℝ → (L2I Vel →L[ℂ] L2I Vel)), IsSelfAdjointExtension (lagrangianCore (lagCanData nu hnu f)) T.op ∧...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_stone_flow` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_stone_flow
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
open BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)

open BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.ChapterStoneResolvent BookProof.StoneBridge BookProof.EsaClosure in

theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_stone_flow (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (L2I Vel)) (U : ℝ → (L2I Vel →L[ℂ] L2I Vel)),
      IsSelfAdjointExtension (lagrangianCore (lagCanData nu hnu f)) T.op ∧ IsStoneFlow T U := by sorry
