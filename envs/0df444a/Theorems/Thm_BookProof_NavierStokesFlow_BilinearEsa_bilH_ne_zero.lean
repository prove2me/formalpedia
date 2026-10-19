-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_bilH_ne_zero
-- name    : BookProof.NavierStokesFlow.BilinearEsa.bilH_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:58:36.705371+00:00
-- url     : https://prove2.me/theorems/86d6c54e-48de-4459-bb9a-b6ecc5030332
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.bilH_ne_zero` (κ : J → ℝ) {j : J} (hj : 0 < κ j) : ∃ x : lpFiniteModes (ℕ × J), bilH κ x ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.bilH_ne_zero` (κ : J → ℝ) {j : J} (hj : 0 < κ j) : ∃ x : lpFiniteModes (ℕ × J), bilH κ x ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.bilH_ne_zero`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.bilH_ne_zero
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

theorem BookProof.NavierStokesFlow.BilinearEsa.bilH_ne_zero (κ : J → ℝ) {j : J} (hj : 0 < κ j) :
    ∃ x : lpFiniteModes (ℕ × J), bilH κ x ≠ 0 := by sorry
