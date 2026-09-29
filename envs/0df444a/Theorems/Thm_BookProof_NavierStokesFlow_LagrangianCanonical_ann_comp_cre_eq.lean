-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_ann_comp_cre_eq
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.ann_comp_cre_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:41:21.923974+00:00
-- url     : https://prove2.me/theorems/c9c99136-9da4-49ff-bcf2-b0994b020c89
-- title:
--   (i : Fin 3) : (ann i).comp (cre i) = (cre i).comp (ann i) + LinearMap.id
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.ann_comp_cre_eq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.ann_comp_cre_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent

theorem BookProof.NavierStokesFlow.LagrangianCanonical.ann_comp_cre_eq (i : Fin 3) :
    (ann i).comp (cre i) = (cre i).comp (ann i) + LinearMap.id := by sorry
