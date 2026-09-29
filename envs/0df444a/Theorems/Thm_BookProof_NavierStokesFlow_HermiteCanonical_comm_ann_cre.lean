-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_comm_ann_cre
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.comm_ann_cre
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:22:33.406666+00:00
-- url     : https://prove2.me/theorems/87d1cbae-ab50-4619-94fe-d12ed59d3ece
-- title:
--   : ann.comp cre - cre.comp ann = LinearMap.id
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.comm_ann_cre` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.comm_ann_cre
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine

theorem BookProof.NavierStokesFlow.HermiteCanonical.comm_ann_cre : ann.comp cre - cre.comp ann = LinearMap.id := by sorry
