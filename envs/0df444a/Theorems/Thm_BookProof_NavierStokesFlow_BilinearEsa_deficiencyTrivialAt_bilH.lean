-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_deficiencyTrivialAt_bilH
-- name    : BookProof.NavierStokesFlow.BilinearEsa.deficiencyTrivialAt_bilH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:58:08.947717+00:00
-- url     : https://prove2.me/theorems/9feebb00-cd32-455e-99a0-4c2ccc42d4a5
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.deficiencyTrivialAt_bilH` (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (z : ℂ) (hblk : ∀ j, DeficiencyTrivialAt (lpFiniteModes ℕ) ((nsH (κ j) (hκ j)).com
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.deficiencyTrivialAt_bilH` (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (z : ℂ) (hblk : ∀ j, DeficiencyTrivialAt (lpFiniteModes ℕ) ((nsH (κ j) (hκ j)).comp (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (κ j))))) z) : DeficiencyTrivialAt (lpFiniteModes (ℕ × J)) (bilH κ) z
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.deficiencyTrivialAt_bilH`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.deficiencyTrivialAt_bilH
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

theorem BookProof.NavierStokesFlow.BilinearEsa.deficiencyTrivialAt_bilH (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (z : ℂ)
    (hblk : ∀ j, DeficiencyTrivialAt (lpFiniteModes ℕ)
      ((nsH (κ j) (hκ j)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (κ j))))) z) :
    DeficiencyTrivialAt (lpFiniteModes (ℕ × J)) (bilH κ) z := by sorry
