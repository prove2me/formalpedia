-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_bilH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.BilinearEsa.bilH_essentiallySelfAdjointOn_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:58:15.88393+00:00
-- url     : https://prove2.me/theorems/e819674e-32cf-4ab2-b35b-dbbf2be3b0a9
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.bilH_essentiallySelfAdjointOn_core` (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) : EssentiallySelfAdjointOn (lpFiniteModes (ℕ × J)) (bilH κ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.bilH_essentiallySelfAdjointOn_core` (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) : EssentiallySelfAdjointOn (lpFiniteModes (ℕ × J)) (bilH κ)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.bilH_essentiallySelfAdjointOn_core`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.bilH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.NavierStokesFlow.BilinearEsa.bilH_essentiallySelfAdjointOn_core (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) :
    EssentiallySelfAdjointOn (lpFiniteModes (ℕ × J)) (bilH κ) := by sorry
