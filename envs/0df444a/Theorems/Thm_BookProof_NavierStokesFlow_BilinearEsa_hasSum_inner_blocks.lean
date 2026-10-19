-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_hasSum_inner_blocks
-- name    : BookProof.NavierStokesFlow.BilinearEsa.hasSum_inner_blocks
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:57:51.778634+00:00
-- url     : https://prove2.me/theorems/9f1005d8-c51a-4c76-b6c7-0efaff84ecc9
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.hasSum_inner_blocks` (x y : L2I (ℕ × J)) : HasSum (fun j : J => (inner ℂ (blockVec x j) (blockVec y j) : ℂ)) (inner ℂ x y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.hasSum_inner_blocks` (x y : L2I (ℕ × J)) : HasSum (fun j : J => (inner ℂ (blockVec x j) (blockVec y j) : ℂ)) (inner ℂ x y)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.hasSum_inner_blocks`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.hasSum_inner_blocks
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

theorem BookProof.NavierStokesFlow.BilinearEsa.hasSum_inner_blocks (x y : L2I (ℕ × J)) :
    HasSum (fun j : J => (inner ℂ (blockVec x j) (blockVec y j) : ℂ)) (inner ℂ x y) := by sorry
