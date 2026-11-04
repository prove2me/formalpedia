-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineBlock_blockVec_affBlockH
-- name    : BookProof.NavierStokesFlow.AffineBlock.blockVec_affBlockH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T13:58:42.447342+00:00
-- url     : https://prove2.me/theorems/b44cd058-ca00-4517-9435-8d567647e49f
-- title:
--   `BookProof.NavierStokesFlow.AffineBlock.blockVec_affBlockH` (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) (v : lpFiniteModes (ℕ × J)) (j : J) : blockVec ((affBlockH κ c hκ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineBlockEsa`.
--
--   `BookProof.NavierStokesFlow.AffineBlock.blockVec_affBlockH` (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) (v : lpFiniteModes (ℕ × J)) (j : J) : blockVec ((affBlockH κ c hκ hc v : L2I (ℕ × J))) j = affH (hκ j) (hc j) ⟨blockVec ((v : L2I (ℕ × J))) j, blockVec_mem_maxDom' _ v j⟩
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineBlock.blockVec_affBlockH`.

-- Generated from ChapterNavierStokesAffineBlockEsa.lean — theorem BookProof.NavierStokesFlow.AffineBlock.blockVec_affBlockH
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineBlockEsaPromoted
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineBlock


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa

variable {J : Type*}

theorem BookProof.NavierStokesFlow.AffineBlock.blockVec_affBlockH (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j)
    (v : lpFiniteModes (ℕ × J)) (j : J) :
    blockVec ((affBlockH κ c hκ hc v : L2I (ℕ × J))) j
      = affH (hκ j) (hc j)
          ⟨blockVec ((v : L2I (ℕ × J))) j, blockVec_mem_maxDom' _ v j⟩ := by sorry
