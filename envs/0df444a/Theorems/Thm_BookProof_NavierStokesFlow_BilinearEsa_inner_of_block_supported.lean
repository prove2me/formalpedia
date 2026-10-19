-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_inner_of_block_supported
-- name    : BookProof.NavierStokesFlow.BilinearEsa.inner_of_block_supported
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:57:33.870544+00:00
-- url     : https://prove2.me/theorems/9a65a7c4-035e-43d9-aaf3-4e8b97945b15
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.inner_of_block_supported` (j : J) (x : L2I (ℕ × J)) (a : L2I ℕ) (hx : ∀ p, (x : ℕ × J → ℂ) p = embFun j ((a : ℕ → ℂ)) p) (w : L2I (ℕ...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.inner_of_block_supported` (j : J) (x : L2I (ℕ × J)) (a : L2I ℕ) (hx : ∀ p, (x : ℕ × J → ℂ) p = embFun j ((a : ℕ → ℂ)) p) (w : L2I (ℕ × J)) : (inner ℂ x w : ℂ) = inner ℂ a (blockVec w j)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.inner_of_block_supported`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.inner_of_block_supported
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

theorem BookProof.NavierStokesFlow.BilinearEsa.inner_of_block_supported (j : J) (x : L2I (ℕ × J)) (a : L2I ℕ)
    (hx : ∀ p, (x : ℕ × J → ℂ) p = embFun j ((a : ℕ → ℂ)) p) (w : L2I (ℕ × J)) :
    (inner ℂ x w : ℂ) = inner ℂ a (blockVec w j) := by sorry
