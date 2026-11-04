-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_blockVec_bilH
-- name    : BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T13:59:18.115324+00:00
-- url     : https://prove2.me/theorems/c8e418d5-2300-4bc3-a5e6-f0172eefcb96
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH` (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (v : lpFiniteModes (ℕ × J)) (j : J) : blockVec ((bilH κ v : L2I (ℕ × J))) j = nsH (κ j) (hκ j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH` (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (v : lpFiniteModes (ℕ × J)) (j : J) : blockVec ((bilH κ v : L2I (ℕ × J))) j = nsH (κ j) (hκ j) ⟨blockVec ((v : L2I (ℕ × J))) j, blockVec_mem_maxDom κ v j⟩
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_blockVec_mem_maxDom
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

theorem BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (v : lpFiniteModes (ℕ × J)) (j : J) :
    blockVec ((bilH κ v : L2I (ℕ × J))) j
      = nsH (κ j) (hκ j) ⟨blockVec ((v : L2I (ℕ × J))) j, blockVec_mem_maxDom κ v j⟩ := by sorry
