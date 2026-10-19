-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_blockVec_mem_maxDom
-- name    : BookProof.NavierStokesFlow.BilinearEsa.blockVec_mem_maxDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:57:57.882604+00:00
-- url     : https://prove2.me/theorems/43577b0c-1135-4030-90c1-c3b159b3e819
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.blockVec_mem_maxDom` (κ : J → ℝ) (v : lpFiniteModes (ℕ × J)) (j : J) : (blockVec ((v : L2I (ℕ × J))) j) ∈ maxDom (oscSymbol (κ j))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.blockVec_mem_maxDom` (κ : J → ℝ) (v : lpFiniteModes (ℕ × J)) (j : J) : (blockVec ((v : L2I (ℕ × J))) j) ∈ maxDom (oscSymbol (κ j))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.blockVec_mem_maxDom`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.blockVec_mem_maxDom
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

theorem BookProof.NavierStokesFlow.BilinearEsa.blockVec_mem_maxDom (κ : J → ℝ) (v : lpFiniteModes (ℕ × J)) (j : J) :
    (blockVec ((v : L2I (ℕ × J))) j) ∈ maxDom (oscSymbol (κ j)) := by sorry
