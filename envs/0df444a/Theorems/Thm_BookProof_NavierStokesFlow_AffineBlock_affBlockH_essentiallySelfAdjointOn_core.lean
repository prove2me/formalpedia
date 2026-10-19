-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineBlock_affBlockH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.AffineBlock.affBlockH_essentiallySelfAdjointOn_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:57:07.208828+00:00
-- url     : https://prove2.me/theorems/d17c8539-f86f-4fbe-bae2-8c0495bbccf5
-- title:
--   `BookProof.NavierStokesFlow.AffineBlock.affBlockH_essentiallySelfAdjointOn_core` (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) : EssentiallySelfAdjointOn (lpFiniteModes (ℕ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineBlockEsa`.
--
--   `BookProof.NavierStokesFlow.AffineBlock.affBlockH_essentiallySelfAdjointOn_core` (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) : EssentiallySelfAdjointOn (lpFiniteModes (ℕ × J)) (affBlockH κ c hκ hc)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineBlock.affBlockH_essentiallySelfAdjointOn_core`.

-- Generated from ChapterNavierStokesAffineBlockEsa.lean — theorem BookProof.NavierStokesFlow.AffineBlock.affBlockH_essentiallySelfAdjointOn_core
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

theorem BookProof.NavierStokesFlow.AffineBlock.affBlockH_essentiallySelfAdjointOn_core (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j)
    (hc : ∀ j, 0 ≤ c j) :
    EssentiallySelfAdjointOn (lpFiniteModes (ℕ × J)) (affBlockH κ c hκ hc) := by sorry
