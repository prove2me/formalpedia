-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineBlock_deficiencyTrivialAt_affBlockH
-- name    : BookProof.NavierStokesFlow.AffineBlock.deficiencyTrivialAt_affBlockH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:57:17.334836+00:00
-- url     : https://prove2.me/theorems/786bbc67-5ea2-42b4-848f-1d0dc12c6c6e
-- title:
--   `BookProof.NavierStokesFlow.AffineBlock.deficiencyTrivialAt_affBlockH` (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) (z : ℂ) (hblk : ∀ j, DeficiencyTrivialAt (lpFiniteModes
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineBlockEsa`.
--
--   `BookProof.NavierStokesFlow.AffineBlock.deficiencyTrivialAt_affBlockH` (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) (z : ℂ) (hblk : ∀ j, DeficiencyTrivialAt (lpFiniteModes ℕ) ((affH (hκ j) (hc j)).comp (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu (κ j) (c j)))))) z) : DeficiencyTrivialAt (lpFiniteModes (ℕ × J)) (affBlockH κ c hκ hc) z
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineBlock.deficiencyTrivialAt_affBlockH`.

-- Generated from ChapterNavierStokesAffineBlockEsa.lean — theorem BookProof.NavierStokesFlow.AffineBlock.deficiencyTrivialAt_affBlockH
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineBlock


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa

variable {J : Type*}

theorem BookProof.NavierStokesFlow.AffineBlock.deficiencyTrivialAt_affBlockH (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j)
    (z : ℂ)
    (hblk : ∀ j, DeficiencyTrivialAt (lpFiniteModes ℕ)
      ((affH (hκ j) (hc j)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu (κ j) (c j)))))) z) :
    DeficiencyTrivialAt (lpFiniteModes (ℕ × J)) (affBlockH κ c hκ hc) z := by sorry
