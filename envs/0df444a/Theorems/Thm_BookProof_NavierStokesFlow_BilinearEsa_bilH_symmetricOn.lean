-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_bilH_symmetricOn
-- name    : BookProof.NavierStokesFlow.BilinearEsa.bilH_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:58:02.640456+00:00
-- url     : https://prove2.me/theorems/8bd8d229-d1ad-4d7d-a51a-e8d134c50261
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.bilH_symmetricOn` (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) : SymmetricOn (lpFiniteModes (ℕ × J)) (bilH κ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.bilH_symmetricOn` (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) : SymmetricOn (lpFiniteModes (ℕ × J)) (bilH κ)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.bilH_symmetricOn`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.bilH_symmetricOn
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

theorem BookProof.NavierStokesFlow.BilinearEsa.bilH_symmetricOn (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) :
    SymmetricOn (lpFiniteModes (ℕ × J)) (bilH κ) := by sorry
