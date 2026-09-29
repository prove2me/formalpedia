-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_comm_mom_pos
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.comm_mom_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:23:17.932928+00:00
-- url     : https://prove2.me/theorems/23211e06-4d8b-4870-803a-567ff11473bc
-- title:
--   (hκ : 0 < κ) : (mom κ).comp (pos κ) - (pos κ).comp (mom κ) = (-Complex.I) • LinearMap.id
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.comm_mom_pos` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.comm_mom_pos
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}

theorem BookProof.NavierStokesFlow.HermiteCanonical.comm_mom_pos (hκ : 0 < κ) :
    (mom κ).comp (pos κ) - (pos κ).comp (mom κ) = (-Complex.I) • LinearMap.id := by sorry
