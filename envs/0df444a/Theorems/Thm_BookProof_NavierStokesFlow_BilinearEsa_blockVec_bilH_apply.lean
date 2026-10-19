-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_blockVec_bilH_apply
-- name    : BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:57:38.670733+00:00
-- url     : https://prove2.me/theorems/06a0f8cb-e138-4378-b334-4914edd46699
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH_apply` (κ : J → ℝ) (x : lpFiniteModes (ℕ × J)) (j : J) (n : ℕ) : ((bilH κ x : L2I (ℕ × J)) : ℕ × J → ℂ) (n, j) = hFun...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH_apply` (κ : J → ℝ) (x : lpFiniteModes (ℕ × J)) (j : J) (n : ℕ) : ((bilH κ x : L2I (ℕ × J)) : ℕ × J → ℂ) (n, j) = hFun (κ j) (fun m => ((x : L2I (ℕ × J)) : ℕ × J → ℂ) (m, j)) n
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH_apply`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH_apply
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

theorem BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH_apply (κ : J → ℝ) (x : lpFiniteModes (ℕ × J)) (j : J) (n : ℕ) :
    ((bilH κ x : L2I (ℕ × J)) : ℕ × J → ℂ) (n, j)
      = hFun (κ j) (fun m => ((x : L2I (ℕ × J)) : ℕ × J → ℂ) (m, j)) n := by sorry
