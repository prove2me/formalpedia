-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineBlock_blockVec_mem_maxDom_prime
-- name    : BookProof.NavierStokesFlow.AffineBlock.blockVec_mem_maxDom_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:42:33.593539+00:00
-- url     : https://prove2.me/theorems/6fa380af-19e4-4fc0-80e6-0b4603ddb2ad
-- title:
--   BookProof.NavierStokesFlow.AffineBlock.blockVec_mem_maxDom'
-- statement:
--   BookProof.NavierStokesFlow.AffineBlock.blockVec_mem_maxDom'

-- Generated from ChapterNavierStokesAffineBlockEsa.lean — theorem BookProof.NavierStokesFlow.AffineBlock.blockVec_mem_maxDom'
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineBlock


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa

variable {J : Type*}

theorem BookProof.NavierStokesFlow.AffineBlock.blockVec_mem_maxDom_prime (s : ℕ → ℝ) (v : lpFiniteModes (ℕ × J)) (j : J) :
    (blockVec ((v : L2I (ℕ × J))) j) ∈ maxDom s := by sorry
