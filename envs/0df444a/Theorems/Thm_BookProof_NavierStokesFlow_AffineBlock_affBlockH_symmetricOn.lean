-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineBlock_affBlockH_symmetricOn
-- name    : BookProof.NavierStokesFlow.AffineBlock.affBlockH_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:57:07.355392+00:00
-- url     : https://prove2.me/theorems/6027f457-50a5-4e2b-a8a7-dd22d864dcfb
-- title:
--   `BookProof.NavierStokesFlow.AffineBlock.affBlockH_symmetricOn` (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) : SymmetricOn (lpFiniteModes (ℕ × J)) (affBlockH κ c hκ hc)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineBlockEsa`.
--
--   `BookProof.NavierStokesFlow.AffineBlock.affBlockH_symmetricOn` (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) : SymmetricOn (lpFiniteModes (ℕ × J)) (affBlockH κ c hκ hc)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineBlock.affBlockH_symmetricOn`.

-- Generated from ChapterNavierStokesAffineBlockEsa.lean — theorem BookProof.NavierStokesFlow.AffineBlock.affBlockH_symmetricOn
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

theorem BookProof.NavierStokesFlow.AffineBlock.affBlockH_symmetricOn (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) :
    SymmetricOn (lpFiniteModes (ℕ × J)) (affBlockH κ c hκ hc) := by sorry
